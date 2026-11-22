//! Port of `tla2sany/modanalyzer/{SpecObj,ParseUnit,ModulePointer,ModuleContext}.java`: loading a specification =
//! locating, parsing and relating the modules reachable through EXTENDS / INSTANCE, in SANY's discovery order.

use crate::ast::{DefBody, Module, Unit};
use crate::parser::{parse_source, ParseError};
use crate::resolve::{Located, Origin, Resolver};
use std::collections::HashMap;
use std::io::Write;
use std::path::Path;

pub type UnitId = usize;
pub type ModId = usize;

pub struct ParseUnit {
    pub name: String,
    pub display_path: String,
    pub origin: Origin,
    pub module: Module,
    pub root: ModId,
    pub extendees: Vec<UnitId>,
    pub instancees: Vec<UnitId>,
    pub is_library: bool,
}

pub struct ModPtr {
    pub name: String,
    pub unit: UnitId,
    /// indices into nested `Unit::Module` positions: path from the unit's root module
    pub path: Vec<usize>,
    pub extends: Vec<String>,
    pub instances: Vec<String>,
    pub inner: Vec<ModId>,
    pub outer: Option<ModId>,
    pub ctx: HashMap<String, ModId>,
}

pub struct SpecObj {
    pub root_file: String,
    pub name: String,
    pub units: Vec<ParseUnit>,
    pub unit_by_name: HashMap<String, UnitId>,
    pub mods: Vec<ModPtr>,
    pub semantic_order: Vec<String>,
    pub root_unit: UnitId,
}

impl SpecObj {
    pub fn module_ast(&self, id: ModId) -> &Module {
        let mp = &self.mods[id];
        let mut m = &self.units[mp.unit].module;
        for &i in &mp.path {
            match &m.units[i] {
                Unit::Module(inner) => m = inner,
                _ => unreachable!(),
            }
        }
        m
    }
}

/// failure of `loadSpec`
pub struct LoadError {
    /// text SANY prints (after the progress lines already written to `out`)
    pub text: String,
    /// markers recognized by the harness are contained in `text`
    pub exit: i32,
}

fn loc_module(name: &str) -> String {
    format!("In module {}", name)
}

fn fatal_abort(file: &str, loc: &str, msg: &str) -> String {
    // Fatal errors while parsing ... + e.toString() + parseErrors.toString()
    format!(
        "\nFatal errors while parsing TLA+ spec in file {}\n{}\n\n{}\n*** Errors: 1\n\n{}\n\n{}\n\n\n",
        file, loc, msg, loc, msg
    )
}

struct Loader<'a> {
    spec: SpecObj,
    resolver: &'a Resolver,
    out: &'a mut dyn Write,
    // search results
    next_name: String,
    next_extender: ModId,
    extension_found: bool,
    instantiation_found: bool,
    root_source: String,
}

impl<'a> Loader<'a> {
    fn parse_unit_text(&mut self, name: &str, loc: &Located, display: &str, first: bool) -> Result<UnitId, LoadError> {
        let _ = first;
        let _ = writeln!(self.out, "Parsing file {}", display);
        let _ = self.out.flush();
        let parsed = match parse_source(&loc.source) {
            Ok(p) => p,
            Err(ParseError { text }) => {
                let _ = writeln!(self.out, "{}", text);
                let txt = format!(
                    "\nFatal errors while parsing TLA+ spec in file {}\n{}\n\nCould not parse module {} from file {}\n*** Errors: 1\n\n{}\n\nCould not parse module {} from file {}\n\n\n",
                    self.spec.root_file,
                    loc_module(name),
                    name,
                    display,
                    loc_module(name),
                    name,
                    display
                );
                return Err(LoadError { text: txt, exit: -1 });
            }
        };
        let module = parsed.module;
        // module name must equal file name
        if &*module.name != name {
            return Err(LoadError {
                text: fatal_abort(
                    &self.spec.root_file,
                    "Unknown location",
                    &format!("File name '{}' does not match the name '{}' of the top level module it contains.", name, module.name),
                ),
                exit: -1,
            });
        }
        let uid = self.spec.units.len();
        // build module pointers
        let root = self.build_mods(&module, uid, vec![], None);
        self.spec.units.push(ParseUnit {
            name: name.to_string(),
            display_path: display.to_string(),
            origin: loc.origin.clone(),
            module,
            root,
            extendees: vec![],
            instancees: vec![],
            is_library: loc.is_library_module(),
        });
        self.spec.unit_by_name.insert(name.to_string(), uid);
        Ok(uid)
    }

    /// `ParseUnit.determineModuleRelationships` + `calculateContextWithinParseUnit`
    fn build_mods(&mut self, m: &Module, unit: UnitId, path: Vec<usize>, outer: Option<ModId>) -> ModId {
        let id = self.spec.mods.len();
        self.spec.mods.push(ModPtr {
            name: m.name.to_string(),
            unit,
            path: path.clone(),
            extends: m.extends.iter().map(|e| e.name.to_string()).collect(),
            instances: m.instances.iter().map(|n| n.to_string()).collect(),
            inner: vec![],
            outer,
            ctx: HashMap::new(),
        });
        // calculateContextWithinParseUnit
        let mut ctx: HashMap<String, ModId> = HashMap::new();
        if let Some(p) = outer {
            for (k, v) in &self.spec.mods[p].ctx {
                ctx.entry(k.clone()).or_insert(*v);
            }
            let mut cur_outer = outer;
            while let Some(par) = cur_outer {
                for (k, v) in &self.spec.mods[par].ctx {
                    ctx.entry(k.clone()).or_insert(*v);
                }
                let peers = self.spec.mods[par].inner.clone();
                // peers defined so far (the module being built is not pushed to `inner` yet)
                for &pe in peers.iter() {
                    let nm = self.spec.mods[pe].name.clone();
                    ctx.entry(nm).or_insert(pe);
                }
                cur_outer = self.spec.mods[par].outer;
            }
        }
        self.spec.mods[id].ctx = ctx;
        // handleExtensions(current, current)
        self.handle_extensions(id, id);
        // inner modules, in order
        let mut idx_path = path;
        for (i, u) in m.units.iter().enumerate() {
            if let Unit::Module(inner) = u {
                idx_path.push(i);
                let child = self.build_mods(inner, unit, idx_path.clone(), Some(id));
                idx_path.pop();
                self.spec.mods[id].inner.push(child);
            }
        }
        id
    }

    fn handle_extensions(&mut self, current: ModId, other: ModId) {
        let extendee_names = self.spec.mods[other].extends.clone();
        for en in extendee_names {
            if let Some(&res) = self.spec.mods[current].ctx.get(&en) {
                let inner = self.spec.mods[res].inner.clone();
                for up in inner {
                    let nm = self.spec.mods[up].name.clone();
                    self.spec.mods[current].ctx.entry(nm).or_insert(up);
                    self.handle_extensions(current, res);
                }
            }
        }
    }

    fn find_or_create(&mut self, name: &str, first: bool, root_path: Option<&Path>) -> Result<UnitId, LoadError> {
        if let Some(&u) = self.spec.unit_by_name.get(name) {
            return Ok(u);
        }
        let located = if first {
            // the root file is given as a path
            let p = root_path.expect("root path");
            match std::fs::read(p) {
                Ok(b) => Some(Located {
                    module: name.to_string(),
                    origin: Origin::User(p.to_path_buf()),
                    source: String::from_utf8_lossy(&b).into_owned(),
                }),
                Err(_) => None,
            }
        } else {
            self.resolver.locate(name).or_else(|| self.monolith_module(name))
        };
        match located {
            Some(l) => {
                let display = match &l.origin {
                    Origin::User(p) if p == Path::new("") => {
                        format!("{}/{}.tla ({})", crate::resolve::STANDARD_DIR_DISPLAY, name, self.spec.root_file)
                    }
                    Origin::User(p) | Origin::Library(p) => abs_display(p),
                    Origin::Standard => format!("{}/{}.tla", crate::resolve::STANDARD_DIR_DISPLAY, name),
                };
                self.parse_unit_text(name, &l, &display, first)
            }
            None => {
                if first {
                    Err(LoadError {
                        text: format!(
                            "\nFatal errors while parsing TLA+ spec in file {}\nUnknown location\n\nCannot find source file for module {}\n*** Errors: 1\n\nUnknown location\n\nCannot find source file for module {}\n\n\n",
                            self.spec.root_file, name, name
                        ),
                        exit: -1,
                    })
                } else {
                    let extender = self.spec.mods[self.next_extender].name.clone();
                    let msg = format!("Cannot find source file for module {} imported in module {}.", name, extender);
                    Err(LoadError { text: fatal_abort(&self.spec.root_file, &loc_module(&extender), &msg), exit: -1 })
                }
            }
        }
    }

    /// `MonolithSpecExtractor.module`: a module defined further down in the root file
    fn monolith_module(&self, name: &str) -> Option<Located> {
        let mut out = String::new();
        let mut active = false;
        for line in self.root_source.lines() {
            if active && line.starts_with("====") {
                out.push_str(line);
                out.push('\n');
                break;
            }
            if !active && is_module_marker(line, name) {
                active = true;
                out.push_str(line);
                out.push('\n');
                continue;
            }
            if active {
                out.push_str(line);
                out.push('\n');
            }
        }
        if !active {
            return None;
        }
        Some(Located { module: name.to_string(), origin: Origin::User(std::path::PathBuf::from("")), source: out })
    }

    fn resolve(&self, m: ModId, name: &str) -> Option<ModId> {
        self.spec.mods[m].ctx.get(name).copied()
    }

    fn find_next_unresolved_extension(&mut self, root: ModId) -> bool {
        let mut visited = std::collections::HashSet::new();
        self.find_ext_body(root, &mut visited)
    }

    fn find_ext_body(&mut self, cur: ModId, visited: &mut std::collections::HashSet<ModId>) -> bool {
        if !visited.insert(cur) {
            self.extension_found = false;
            return false;
        }
        let extendees = self.spec.mods[cur].extends.clone();
        let instancees = self.spec.mods[cur].instances.clone();
        for e in &extendees {
            if self.resolve(cur, e).is_none() {
                self.next_name = e.clone();
                self.next_extender = cur;
                self.extension_found = true;
                return true;
            }
        }
        for e in &extendees {
            if let Some(r) = self.resolve(cur, e) {
                if self.find_ext_body(r, visited) {
                    self.extension_found = true;
                    return true;
                }
            }
        }
        for i in &instancees {
            if let Some(r) = self.resolve(cur, i) {
                if self.find_ext_body(r, visited) {
                    self.extension_found = true;
                    return true;
                }
            }
        }
        let inner = self.spec.mods[cur].inner.clone();
        for im in inner {
            if self.find_ext_body(im, visited) {
                self.extension_found = true;
                return true;
            }
        }
        self.extension_found = false;
        false
    }

    fn find_next_unresolved_instantiation(&mut self, root: ModId) -> bool {
        let mut visited = std::collections::HashSet::new();
        self.find_inst_body(root, &mut visited)
    }

    fn find_inst_body(&mut self, cur: ModId, visited: &mut std::collections::HashSet<ModId>) -> bool {
        if !visited.insert(cur) {
            self.instantiation_found = false;
            return false;
        }
        let extendees = self.spec.mods[cur].extends.clone();
        let instancees = self.spec.mods[cur].instances.clone();
        for i in &instancees {
            if self.resolve(cur, i).is_none() && !self.instance_resolves_to_internal(cur, i) {
                self.next_name = i.clone();
                self.next_extender = cur;
                self.instantiation_found = true;
                return true;
            }
        }
        for e in &extendees {
            if let Some(r) = self.resolve(cur, e) {
                if self.find_inst_body(r, visited) {
                    self.instantiation_found = true;
                    return true;
                }
            }
        }
        for i in &instancees {
            if let Some(r) = self.resolve(cur, i) {
                if self.find_inst_body(r, visited) {
                    self.instantiation_found = true;
                    return true;
                }
            }
        }
        let inner = self.spec.mods[cur].inner.clone();
        for im in inner {
            if self.find_inst_body(im, visited) {
                self.instantiation_found = true;
                return true;
            }
        }
        self.instantiation_found = false;
        false
    }

    fn instance_resolves_to_internal(&self, cur: ModId, instancee: &str) -> bool {
        let m = self.spec.module_ast(cur);
        let mut seen: Vec<String> = Vec::new();
        for u in &m.units {
            match u {
                Unit::Module(inner) => seen.push(inner.name.to_string()),
                Unit::Instance(i) => {
                    if &*i.inst.module == instancee {
                        return seen.iter().any(|s| s == instancee);
                    }
                }
                Unit::OpDef(d) => {
                    if let DefBody::Instance(inst) = &d.body {
                        if &*inst.module == instancee {
                            return seen.iter().any(|s| s == instancee);
                        }
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn directly_extends(&self, m1: ModId, m2: ModId) -> bool {
        self.spec.mods[m1].extends.iter().any(|e| self.resolve(m1, e) == Some(m2))
    }

    fn modules_indirectly_extending(&self, module: ModId) -> Vec<ModId> {
        let mut extenders = vec![module];
        let mut start = 0;
        let mut end = extenders.len();
        let mut additions = true;
        while additions {
            additions = false;
            let mut i = start;
            while i < end {
                for mp in 0..self.spec.mods.len() {
                    if self.directly_extends(mp, extenders[i]) {
                        extenders.push(mp);
                        additions = true;
                    }
                }
                start = end;
                end = extenders.len();
                i += 1;
            }
            if !additions {
                break;
            }
        }
        extenders
    }

    fn resolve_names_extension(&mut self, extender: ModId, extendee_unit: UnitId) {
        let ename = self.spec.units[extendee_unit].name.clone();
        let eroot = self.spec.units[extendee_unit].root;
        self.spec.mods[extender].ctx.entry(ename).or_insert(eroot);
        let ext = self.modules_indirectly_extending(extender);
        for m in ext {
            self.resolve_module_and_extension(m, extendee_unit);
        }
    }

    fn resolve_module_and_extension(&mut self, ext_mod: ModId, extendee_unit: UnitId) {
        let ext_names = self.spec.mods[ext_mod].extends.clone();
        let inst_names = self.spec.mods[ext_mod].instances.clone();
        let eroot = self.spec.units[extendee_unit].root;
        let inner = self.spec.mods[eroot].inner.clone();
        for nm in ext_names.iter().chain(inst_names.iter()) {
            for &im in &inner {
                if &self.spec.mods[im].name == nm {
                    self.spec.mods[ext_mod].ctx.entry(nm.clone()).or_insert(im);
                    break;
                }
            }
        }
        let mine = self.spec.mods[ext_mod].inner.clone();
        for ni in mine {
            self.resolve_module_and_extension(ni, extendee_unit);
        }
    }

    fn non_circularity_test(&self, unit: UnitId) -> Result<(), LoadError> {
        let mut visited = std::collections::HashSet::new();
        let mut path = vec![unit];
        self.non_circ_body(unit, unit, &mut visited, &mut path)
    }

    fn non_circ_body(
        &self,
        target: UnitId,
        cand: UnitId,
        visited: &mut std::collections::HashSet<UnitId>,
        path: &mut Vec<UnitId>,
    ) -> Result<(), LoadError> {
        if !visited.insert(cand) {
            return Ok(());
        }
        let mut refs: Vec<UnitId> = self.spec.units[cand].extendees.clone();
        for i in &self.spec.units[cand].instancees {
            if !refs.contains(i) {
                refs.push(*i);
            }
        }
        for r in refs {
            if r == target {
                let mut s = String::new();
                for u in path.iter() {
                    s.push_str(&self.spec.units[*u].display_path);
                    s.push_str(" --> ");
                }
                s.push_str(&self.spec.units[path[0]].display_path);
                let msg = format!("Circular dependency among .tla files; dependency cycle is:\n\n  {}", s);
                return Err(LoadError { text: fatal_abort(&self.spec.root_file, "Unknown location", &msg), exit: -1 });
            }
            path.push(r);
            self.non_circ_body(target, r, visited, path)?;
            path.pop();
        }
        Ok(())
    }

    fn calculate_dependencies(&mut self, u: UnitId) {
        let extendees = self.spec.units[u].extendees.clone();
        let instancees = self.spec.units[u].instancees.clone();
        for e in extendees {
            self.calculate_dependencies(e);
        }
        for i in instancees {
            self.calculate_dependencies(i);
        }
        let name = self.spec.units[u].name.clone();
        if !self.spec.semantic_order.contains(&name) {
            self.spec.semantic_order.push(name);
        }
    }
}

/// `-----*\s*MODULE\s+NAME\s*----*` matching the whole line
fn is_module_marker(line: &str, name: &str) -> bool {
    let t = line.trim_end_matches(|c: char| c == '\r');
    let bytes = t.as_bytes();
    let mut i = 0;
    while i < bytes.len() && bytes[i] == b'-' {
        i += 1;
    }
    if i < 4 {
        return false;
    }
    let rest = t[i..].trim_start();
    let rest = match rest.strip_prefix("MODULE") {
        Some(r) => r,
        None => return false,
    };
    if !rest.starts_with(char::is_whitespace) {
        return false;
    }
    let rest = rest.trim_start();
    let rest = match rest.strip_prefix(name) {
        Some(r) => r,
        None => return false,
    };
    let rest = rest.trim_start();
    rest.len() >= 3 && rest.bytes().all(|b| b == b'-')
}

fn abs_display(p: &Path) -> String {
    let abs = std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    let s = abs.to_string_lossy().to_string();
    // strip the Windows verbatim prefix
    s.strip_prefix("\\\\?\\").map(|x| x.to_string()).unwrap_or(s)
}

/// Java `SpecObj.loadSpec`. Progress lines ("Parsing file ...") go to `out`; on failure the error text is
/// returned (the caller prints it).
pub fn load_spec(root_file: &Path, resolver: &Resolver, out: &mut dyn Write) -> Result<SpecObj, LoadError> {
    let stem = root_file.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let spec = SpecObj {
        root_file: abs_display(root_file),
        name: stem.clone(),
        units: vec![],
        unit_by_name: HashMap::new(),
        mods: vec![],
        semantic_order: vec![],
        root_unit: 0,
    };
    let root_source = std::fs::read(root_file).map(|b| String::from_utf8_lossy(&b).into_owned()).unwrap_or_default();
    let mut ld = Loader {
        spec,
        resolver,
        out,
        next_name: String::new(),
        next_extender: 0,
        extension_found: false,
        instantiation_found: false,
        root_source,
    };
    let root_unit = ld.find_or_create(&stem, true, Some(root_file))?;
    ld.spec.root_unit = root_unit;
    let root_mod = ld.spec.units[root_unit].root;
    loop {
        let found = ld.find_next_unresolved_extension(root_mod) || ld.find_next_unresolved_instantiation(root_mod);
        if !found {
            break;
        }
        let name = ld.next_name.clone();
        let unit = if let Some(&u) = ld.spec.unit_by_name.get(&name) { u } else { ld.find_or_create(&name, false, None)? };
        let extender_unit = ld.spec.mods[ld.next_extender].unit;
        if ld.extension_found {
            if !ld.spec.units[extender_unit].extendees.contains(&unit) {
                ld.spec.units[extender_unit].extendees.push(unit);
            }
        }
        if ld.instantiation_found {
            if !ld.spec.units[extender_unit].instancees.contains(&unit) {
                ld.spec.units[extender_unit].instancees.push(unit);
            }
        }
        ld.non_circularity_test(unit)?;
        let ext = ld.next_extender;
        if ld.extension_found {
            ld.resolve_names_extension(ext, unit);
        }
        if ld.instantiation_found {
            let nm = ld.spec.units[unit].name.clone();
            let r = ld.spec.units[unit].root;
            ld.spec.mods[ext].ctx.entry(nm).or_insert(r);
        }
    }
    ld.calculate_dependencies(root_unit);
    Ok(ld.spec)
}
