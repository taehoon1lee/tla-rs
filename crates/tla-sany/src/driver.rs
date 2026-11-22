//! Port of `SANY.frontEndSemanticAnalysis` / `frontEndLinting`: analyse every module in dependency order and
//! print SANY's progress lines, warnings and errors.

use crate::analyze::{Analyzer, SemSpec};
use crate::modules::SpecObj;
use crate::resolve::Origin;
use crate::sem::ModuleNode;
use std::collections::HashMap;
use std::io::Write;
use std::rc::Rc;

pub struct SemOutcome {
    pub spec: Option<SemSpec>,
    /// 0 ok, 4 semantic/level errors
    pub error_level: i32,
}

pub fn analyze_spec(spec: &SpecObj, out: &mut dyn Write, level_check: bool, lint: bool) -> SemOutcome {
    let mut an = Analyzer::new(spec, level_check);
    let mut error_level = 0;
    let mut root: Option<Rc<ModuleNode>> = None;
    for name in spec.semantic_order.iter() {
        if an.table.contains_key(name) {
            continue;
        }
        let unit = match spec.unit_by_name.get(name) {
            Some(&u) => u,
            None => continue,
        };
        let _ = writeln!(out, "Semantic processing of module {}", name);
        let ast = &spec.units[unit].module;
        // each external module is analysed with a fresh symbol table
        an.scopes.clear();
        an.mod_depth_stack.clear();
        an.cur = None;
        let r = an.gen_module(ast, None);
        if let Ok(m) = r {
            m.is_standard.set(matches!(spec.units[unit].origin, Origin::Standard));
            an.table.insert(name.clone(), m.clone());
            root = Some(m);
        }
        let nw = an.errors.warnings.len();
        let ne = an.errors.errors.len();
        if nw + ne > 0 {
            if nw > 0 {
                let _ = writeln!(out, "*** Warnings: {}\n", nw);
                for w in &an.errors.warnings {
                    let _ = write!(out, "{}\n\n\n", w.render());
                }
            }
            if ne > 0 {
                let _ = writeln!(out, "Semantic errors:\n\n*** Errors: {}\n", ne);
                for e in &an.errors.errors {
                    let _ = write!(out, "{}\n\n", e.render());
                }
            }
            if ne > 0 {
                error_level = 4;
            }
        }
    }
    if error_level == 0 && lint && level_check {
        for name in spec.semantic_order.iter() {
            if let Some(m) = an.table.get(name) {
                if m.is_standard.get() {
                    continue;
                }
                let _ = writeln!(out, "Linting of module {}", name);
            }
        }
    }
    let modules: HashMap<String, Rc<ModuleNode>> = an.table.clone();
    let spec_out = root.map(|r| SemSpec { modules, root: r, order: spec.semantic_order.clone() });
    SemOutcome { spec: spec_out, error_level }
}
