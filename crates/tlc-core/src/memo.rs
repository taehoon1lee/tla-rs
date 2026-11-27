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

/// Can evaluating `e` do anything besides computing its value (print, `TLCSet`/`TLCGet`, a random choice, an operator this
/// port does not know)?  `true`: no; its value is a function of the states it is evaluated on (state variables are allowed).
/// The liveness checker shares the value of such a leaf between the orders of solution that contain it (`live.rs`).
pub fn side_effect_free(e: &Expr) -> bool {
    struct S {
        seen: HashSet<usize>,
        steps: usize,
    }
    fn callee(c: &Callee, st: &mut S) -> bool {
        match c {
            Callee::Def(d) => {
                let o = d.original();
                if crate::natives::lookup(&o.module, &o.name).is_some() {
                    return pure_native(&o.module, &o.name);
                }
                if !st.seen.insert(d.id) {
                    return true;
                }
                match d.body() {
                    Some(b) => go(&b, st),
                    None => false,
                }
            }
            Callee::Decl(_) | Callee::Param(_) => true,
        }
    }
    fn arg(a: &Arg, st: &mut S) -> bool {
        match a {
            Arg::Expr(e) => go(e, st),
            Arg::Op(OpArg::Callee(c, _)) => callee(c, st),
            Arg::Op(OpArg::Builtin(..)) => true,
            Arg::Op(OpArg::Lambda(d)) => match d.body() {
                Some(b) => go(&b, st),
                None => false,
            },
        }
    }
    fn go(e: &Expr, st: &mut S) -> bool {
        st.steps += 1;
        if st.steps > 50_000 {
            return false;
        }
        match &e.kind {
            EKind::Unsupported(_) => return false,
            // the substituted values are not children of the node
            EKind::SubstIn(subs, _) => {
                for s in subs.iter() {
                    if !arg(&s.value, st) {
                        return false;
                    }
                }
            }
            EKind::Apply(c, args) => {
                if !callee(c, st) {
                    return false;
                }
                for a in args {
                    if let Arg::Op(_) = a {
                        if !arg(a, st) {
                            return false;
                        }
                    }
                }
            }
            _ => {}
        }
        for c in e.children() {
            if !go(&c, st) {
                return false;
            }
        }
        true
    }
    go(e, &mut S { seen: HashSet::new(), steps: 0 })
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn side_effect_free_rejects_printing_and_tlc_registers() {
        let dir = std::env::temp_dir().join(format!("tlcrs-memo-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = r#"---- MODULE SefTest ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Double(n) == n * 2
Pure == x' = Double(x) /\ Len(<<x>>) = 1
WithLambda == x' = [i \in {1} |-> x][1]
Printing == PrintT(x) /\ x' = x
Level == TLCGet("level") > 0
Indirect == Pure /\ Printing
====
"#;
        std::fs::write(dir.join("SefTest.tla"), src).unwrap();
        let r = tla_sany::Resolver::new(&dir, vec![]);
        let mut out = Vec::new();
        let spec = tla_sany::frontend(&dir.join("SefTest.tla"), &r, &mut out).expect("module parses");
        let sem = spec.sem.expect("semantic tree");
        let body = |n: &str| sem.root.defs.borrow().iter().find(|d| &*d.name == n).and_then(|d| d.body()).expect(n);
        assert!(side_effect_free(&body("Pure")));
        assert!(side_effect_free(&body("WithLambda")));
        assert!(!side_effect_free(&body("Printing")));
        assert!(!side_effect_free(&body("Level")));
        assert!(!side_effect_free(&body("Indirect")));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
