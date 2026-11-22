"""Resolve a TLCRS_SPROF sample file with the COFF symbol table of the executable.
usage: python tmp/symbolize.py samples.txt [exe] [--top N] [--incl]"""
import sys, struct, re, collections

args = [a for a in sys.argv[1:] if not a.startswith("--")]
if "--lines" in sys.argv:
    args.remove(sys.argv[sys.argv.index("--lines") + 1])
if "--callers" in sys.argv:
    args.remove(sys.argv[sys.argv.index("--callers") + 1])
top = int(sys.argv[sys.argv.index("--top") + 1]) if "--top" in sys.argv else 40
if "--top" in sys.argv:
    args.remove(sys.argv[sys.argv.index("--top") + 1])
sp = args[0]
exe = args[1] if len(args) > 1 else "target-prof/release/tlc-rs.exe"
d = open(exe, "rb").read()
pe = struct.unpack_from("<I", d, 0x3C)[0]
nsec, = struct.unpack_from("<H", d, pe + 6)
symptr, nsyms = struct.unpack_from("<II", d, pe + 12)
optsz, = struct.unpack_from("<H", d, pe + 20)
opt = pe + 24
imagebase, = struct.unpack_from("<Q", d, opt + 24)
secs = []
so = opt + optsz
for i in range(nsec):
    name = d[so + i * 40: so + i * 40 + 8].rstrip(b"\0").decode("latin1")
    vsize, va, rawsz, rawptr = struct.unpack_from("<IIII", d, so + i * 40 + 8)
    secs.append((name, va, vsize))
strtab = symptr + nsyms * 18
syms = []
i = 0
while i < nsyms:
    o = symptr + i * 18
    nm = d[o:o + 8]
    if nm[:4] == b"\0\0\0\0":
        off, = struct.unpack("<I", nm[4:])
        e = d.index(b"\0", strtab + off)
        name = d[strtab + off:e].decode("latin1")
    else:
        name = nm.rstrip(b"\0").decode("latin1")
    value, sec, typ, cls, naux = struct.unpack_from("<IhHBB", d, o + 8)
    if sec > 0 and sec <= len(secs) and (typ & 0xF0) == 0x20:   # function symbols
        syms.append((secs[sec - 1][1] + value, name))
    i += 1 + naux
syms.sort()
addrs = [a for a, _ in syms]
import bisect


def demangle(n):
    if n.startswith("_ZN") or n.startswith("ZN"):
        s = n[3:] if n.startswith("_ZN") else n[2:]
        parts = []
        while s and s[0].isdigit():
            m = re.match(r"(\d+)", s)
            k = int(m.group(1))
            parts.append(s[m.end():m.end() + k])
            s = s[m.end() + k:]
        if parts and re.match(r"h[0-9a-f]{16}$", parts[-1]):
            parts.pop()
        out = "::".join(parts)
        for a, b in (("$LT$", "<"), ("$GT$", ">"), ("$u20$", " "), ("$C$", ","), ("$RF$", "&"), ("$LP$", "("), ("$RP$", ")"),
                     ("$u7b$", "{"), ("$u7d$", "}"), ("$BP$", "*"), ("$SP$", "@"), ("..", "::")):
            out = out.replace(a, b)
        return out
    return n


cache = {}
WANT = sys.argv[sys.argv.index("--callers") + 1] if "--callers" in sys.argv else ""
callers = collections.Counter()


def sym(addr, base):
    rva = addr - base
    if rva in cache:
        return cache[rva]
    i = bisect.bisect_right(addrs, rva) - 1
    r = demangle(syms[i][1]) if i >= 0 and rva - addrs[i] < 0x20000 else "?"
    cache[rva] = r
    return r


lines = open(sp).read().split("\n")
base = int(lines[0].split()[1], 16)
selfc, incl = collections.Counter(), collections.Counter()
n = 0
for ln in lines[1:]:
    if not ln.strip():
        continue
    raw = ln.split()
    if "0" in raw:
        z = raw.index("0")
        scan = [sym(int(x, 16) - 1, base) for x in raw[z + 1:]]
        raw = raw[:z]
    else:
        scan = []
    st = [sym(int(x, 16) - 1 if k else int(x, 16), base) for k, x in enumerate(raw)]
    if WANT and WANT in st[0]:
        callers[tuple(scan)] += 1
    n += 1
    selfc[st[0]] += 1
    for f in set(st):
        incl[f] += 1
print(f"{n} samples")
print("== self")
for f, c in selfc.most_common(top):
    print(f"{100 * c / n:5.1f}%  {f[:150]}")
print("== inclusive")
for f, c in incl.most_common(top):
    print(f"{100 * c / n:5.1f}%  {f[:150]}")

if WANT:
    print("== scan callers of", WANT)
    for k, c in callers.most_common(8):
        print(c, " <- ".join(x[-70:] for x in k[:3]))

if "--lines" in sys.argv:
    sys.path.insert(0, __file__.rsplit("\\", 1)[0] if "\\" in __file__ else ".")
    from dwarfline import LineTable
    lt = LineTable(d)
    fn = sys.argv[sys.argv.index("--lines") + 1]
    lc = collections.Counter()
    tot = 0
    for ln in lines[1:]:
        if not ln.strip():
            continue
        raw = ln.split()
        if "0" in raw:
            raw = raw[:raw.index("0")]
        a = int(raw[0], 16) - base
        if fn in sym(a + base, base):
            r = lt.lookup(a)
            lc[(r[0].replace("\\", "/").split("/src/")[-1], r[1]) if r else ("?", 0)] += 1
            tot += 1
    print("== hot lines in", fn, tot)
    for k, c in lc.most_common(top):
        print(f"{100 * c / n:5.1f}%  {k[0]}:{k[1]}")
