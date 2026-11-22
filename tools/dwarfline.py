"""Minimal DWARF .debug_line decoder for a PE/COFF executable (v2-v5).  Provides addr -> (file, line) lookups.
usage as a module:  from dwarfline import LineTable; lt = LineTable(exe_bytes); lt.lookup(rva)"""
import struct, bisect


def uleb(d, o):
    r = s = 0
    while True:
        b = d[o]
        o += 1
        r |= (b & 0x7F) << s
        s += 7
        if not b & 0x80:
            return r, o


def sleb(d, o):
    r = s = 0
    while True:
        b = d[o]
        o += 1
        r |= (b & 0x7F) << s
        s += 7
        if not b & 0x80:
            if b & 0x40:
                r -= 1 << s
            return r, o


def cstr(d, o):
    e = d.index(b"\0", o)
    return d[o:e].decode("utf-8", "replace"), e + 1


class LineTable:
    def __init__(self, exe):
        pe = struct.unpack_from("<I", exe, 0x3C)[0]
        nsec, = struct.unpack_from("<H", exe, pe + 6)
        symptr, nsyms = struct.unpack_from("<II", exe, pe + 12)
        optsz, = struct.unpack_from("<H", exe, pe + 20)
        opt = pe + 24
        self.imagebase, = struct.unpack_from("<Q", exe, opt + 24)
        strtab = symptr + nsyms * 18
        so = opt + optsz
        secs = {}
        for i in range(nsec):
            nm = exe[so + i * 40: so + i * 40 + 8].rstrip(b"\0").decode("latin1")
            if nm.startswith("/"):
                off = int(nm[1:])
                e = exe.index(b"\0", strtab + off)
                nm = exe[strtab + off:e].decode("latin1")
            vsize, va, rawsz, rawptr = struct.unpack_from("<IIII", exe, so + i * 40 + 8)
            secs[nm] = exe[rawptr:rawptr + min(rawsz, vsize if vsize else rawsz)] if rawptr else b""
        self.line = secs.get(".debug_line", b"")
        self.line_str = secs.get(".debug_line_str", b"")
        self.str = secs.get(".debug_str", b"")
        self.rows = []   # (addr, file, line)
        self.files_cache = {}
        self._parse()
        self.rows.sort(key=lambda r: r[0])
        self.addrs = [r[0] for r in self.rows]

    def _form_str(self, d, o, form):
        if form == 0x08:
            return cstr(d, o)
        if form == 0x1F:  # line_strp
            off, = struct.unpack_from("<I", d, o)
            return cstr(self.line_str, off)[0], o + 4
        if form == 0x0E:  # strp
            off, = struct.unpack_from("<I", d, o)
            return cstr(self.str, off)[0], o + 4
        raise ValueError(form)

    def _skip_form(self, d, o, form):
        if form in (0x0B,):
            return o + 1
        if form == 0x05:
            return o + 2
        if form == 0x06:
            return o + 4
        if form == 0x07:
            return o + 8
        if form in (0x0F, 0x0D):
            return (uleb(d, o)[1] if form == 0x0F else sleb(d, o)[1])
        if form == 0x1E:
            return o + 16
        if form == 0x1F or form == 0x0E:
            return o + 4
        if form == 0x08:
            return cstr(d, o)[1]
        raise ValueError(form)

    def _parse(self):
        d = self.line
        o = 0
        while o < len(d):
            ul, = struct.unpack_from("<I", d, o)
            end = o + 4 + ul
            p = o + 4
            ver, = struct.unpack_from("<H", d, p)
            p += 2
            if ver >= 5:
                p += 2  # address_size, seg_selector_size
            hl, = struct.unpack_from("<I", d, p)
            p += 4
            prog = p + hl
            min_inst = d[p]
            p += 1
            if ver >= 4:
                p += 1
            default_is_stmt = d[p]
            line_base = struct.unpack_from("<b", d, p + 1)[0]
            line_range = d[p + 2]
            opbase = d[p + 3]
            p += 4
            oplens = list(d[p:p + opbase - 1])
            p += opbase - 1
            files = []
            if ver >= 5:
                fc = d[p]
                p += 1
                fmts = []
                for _ in range(fc):
                    ct, p = uleb(d, p)
                    fm, p = uleb(d, p)
                    fmts.append((ct, fm))
                nd, p = uleb(d, p)
                dirs = []
                for _ in range(nd):
                    nm = ""
                    for ct, fm in fmts:
                        if ct == 1:
                            nm, p = self._form_str(d, p, fm)
                        else:
                            p = self._skip_form(d, p, fm)
                    dirs.append(nm)
                fc = d[p]
                p += 1
                fmts = []
                for _ in range(fc):
                    ct, p = uleb(d, p)
                    fm, p = uleb(d, p)
                    fmts.append((ct, fm))
                nf, p = uleb(d, p)
                for _ in range(nf):
                    nm, di = "", 0
                    for ct, fm in fmts:
                        if ct == 1:
                            nm, p = self._form_str(d, p, fm)
                        elif ct == 2:
                            di, p = uleb(d, p)
                        else:
                            p = self._skip_form(d, p, fm)
                    files.append((dirs[di] + "/" + nm) if di < len(dirs) and not nm.startswith("/") else nm)
            else:
                dirs = [""]
                while d[p]:
                    s, p = cstr(d, p)
                    dirs.append(s)
                p += 1
                files = [""]
                while d[p]:
                    s, p = cstr(d, p)
                    di, p = uleb(d, p)
                    _, p = uleb(d, p)
                    _, p = uleb(d, p)
                    files.append((dirs[di] + "/" + s) if di and not s.startswith("/") else s)
                p += 1
            # line number program
            addr, file, line = 0, 1, 1
            p = prog
            while p < end:
                op = d[p]
                p += 1
                if op >= opbase:
                    adj = op - opbase
                    addr += (adj // line_range) * min_inst
                    line += line_base + adj % line_range
                    self.rows.append((addr, files[file] if file < len(files) else "?", line))
                elif op == 0:
                    ln, p = uleb(d, p)
                    sub = d[p]
                    if sub == 1:
                        self.rows.append((addr, "END", 0))
                        addr, file, line = 0, 1, 1
                    elif sub == 2:
                        addr = struct.unpack_from("<Q", d, p + 1)[0] if ln == 9 else struct.unpack_from("<I", d, p + 1)[0]
                    p += ln
                elif op == 1:
                    self.rows.append((addr, files[file] if file < len(files) else "?", line))
                elif op == 2:
                    v, p = uleb(d, p)
                    addr += v * min_inst
                elif op == 3:
                    v, p = sleb(d, p)
                    line += v
                elif op == 4:
                    file, p = uleb(d, p)
                elif op == 5:
                    _, p = uleb(d, p)
                elif op == 8:
                    addr += ((255 - opbase) // line_range) * min_inst
                elif op == 9:
                    addr += struct.unpack_from("<H", d, p)[0]
                    p += 2
                else:
                    for _ in range(oplens[op - 1]):
                        _, p = uleb(d, p)
            o = end

    def lookup(self, rva):
        a = self.imagebase + rva
        i = bisect.bisect_right(self.addrs, a) - 1
        if i < 0:
            return None
        r = self.rows[i]
        if r[1] == "END":
            return None
        return r[1], r[2]
