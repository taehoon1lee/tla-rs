//! Memoization of calls of constant-level operators (no counterpart in Java, which re-evaluates them every time).
//!
//! `PermsOf(s) == { s ** f : f \in Automorphisms(DOMAIN s) }` is evaluated for every state of a model although its value
//! only depends on its argument.  A call of a constant-level, parameterized operator is remembered by the values of its
//! arguments when the operator is *pure* (nothing it can reach reads the state, prints, draws a random number, ...) and
//! *builds sets or functions* (so that the result is worth the hashing of the arguments).

use std::collections::HashSet;
use tla_sany::sem::*;

/// operators of the standard modules that are functions of their arguments only
pub(crate) fn pure_native(module: &str, name: &str) -> bool {
    match module {
        "Naturals" | "Integers" | "Reals" | "Sequences" | "FiniteSets" | "Bags" | "FiniteSetsExt" | "SequencesExt" | "Functions" | "Folds"
        | "Graphs" | "UndirectedGraphs" | "DyadicRationals" | "Bitwise" => true,
        "TLC" => matches!(name, ":>" | "@@" | "Permutations" | "SortSeq"),
        _ => false,
    }
}

struct Scan {
    seen: HashSet<usize>,
    heavy: bool,
    steps: usize,
    /// constant declarations (ids) the operator mentions
    decls: Vec<usize>,
    /// an INSTANCE substitution occurs (its value expressions are not visited by `Expr::children`)
    subst_in: bool,
    /// > 0 while scanning the body of a constant-level definition without parameters: it is evaluated once and its value
    /// is cached (`CompiledDef::cache`), so an impure native in it (`RandomElement`) runs once, before any call is remembered
    frozen: u32,
}

fn scan(e: &Expr, st: &mut Scan) -> bool {
    st.steps += 1;
    if st.steps > 20_000 {
        return false;
    }
    match &e.kind {
        EKind::Unsupported(_) => return false,
        EKind::SubstIn(..) => st.subst_in = true,
        EKind::SubsetOf(..) | EKind::SetOfAll(..) | EKind::SetOfFcns(..) | EKind::BQuant { .. } | EKind::Choose(..) | EKind::FcnCons(..) => st.heavy = true,
        EKind::Bi(B::Subset, _) => st.heavy = true,
        EKind::Apply(callee, args) => {
            for a in args {
                if let Arg::Op(_) = a {
                    return false;
                }
            }
            match callee {
                Callee::Def(d) => {
                    let o = d.original();
                    if crate::natives::lookup(&o.module, &o.name).is_some() {
                        if !pure_native(&o.module, &o.name) && st.frozen == 0 {
                            return false;
                        }
                    } else if st.seen.insert(d.id) {
                        if d.params.borrow().iter().any(|p| p.arity > 0) {
                            return false;
                        }
                        let freeze = d.params.borrow().is_empty() && d.level.get() == Level::Const;
                        st.frozen += freeze as u32;
                        let ok = match d.body() {
                            Some(b) => scan(&b, st),
                            None => false,
                        };
                        st.frozen -= freeze as u32;
                        if !ok {
                            return false;
                        }
                    }
                }
                Callee::Decl(dc) => {
                    if dc.kind == DeclKind::Variable {
                        return false;
                    }
                    st.decls.push(dc.id);
                }
                Callee::Param(_) => {}
            }
        }
        _ => {}
    }
    for c in e.children() {
        if !scan(&c, st) {
            return false;
        }
    }
    true
}

/// may calls of this constant-level, parameterized definition be remembered?  `Some(decls)`: yes; `decls` lists the constant
/// declarations it can reach, or `None` when it contains INSTANCE substitutions (then calls are only remembered while no
/// substitution is in scope: an enclosing INSTANCE may substitute the declarations it reaches)
pub fn memoizable(d: &std::rc::Rc<OpDef>) -> Option<Option<Vec<usize>>> {
    if d.params.borrow().iter().any(|p| p.arity > 0) {
        return None;
    }
    let body = d.body()?;
    let mut st = Scan { seen: HashSet::new(), heavy: false, steps: 0, decls: Vec::new(), subst_in: false, frozen: 0 };
    st.seen.insert(d.id);
    if scan(&body, &mut st) && (st.heavy || st.steps >= 12) {
        Some(if st.subst_in { None } else { Some(st.decls) })
    } else {
        None
    }
}
