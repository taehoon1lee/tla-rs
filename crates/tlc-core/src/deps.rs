//! Variable dependencies of state-level definitions (no counterpart in Java).
//!
//! Java's `LazyValue` keeps the value of a nullary definition together with a copy of the states it was computed in and
//! reuses it while every variable that was assigned *then* has the same value (`TLCState.isSubset`).  We do the same, but
//! with the variables the definition actually reads: `totalOpOrder` of InnerSerial reads `opQ` only, so its value survives
//! the many assignments of the other primed variables (`opOrder'`) that are tried one after the other.
//!
//! `state_reads` walks the compiled body (and everything it calls) and returns the sorted variable indices it reads, or
//! `None` when the value may depend on anything else: primed variables, `UNCHANGED`, `ENABLED`, temporal operators,
//! operator parameters, INSTANCE substitutions, or natives that print / read the environment / draw random numbers.

use crate::ir::*;
use std::collections::HashSet;
use std::rc::Rc;
use tla_sany::sem::B;

struct Walk {
    vars: Vec<u32>,
    seen: HashSet<usize>,
    steps: usize,
}

/// the state variables (indices) read by the nullary definition `d`, or `None` when its value is not a function of them
pub fn state_reads(d: &Rc<CompiledDef>) -> Option<Vec<u32>> {
    let mut w = Walk { vars: Vec::new(), seen: HashSet::new(), steps: 0 };
    if !w.def(d) {
        return None;
    }
    w.vars.sort_unstable();
    w.vars.dedup();
    Some(w.vars)
}

/// the expression reads state variables, constants and frame slots only: no primed variables, no impure natives, no
/// operator parameters, no INSTANCE substitutions (so evaluating it earlier or later in the same states gives the same value)
pub fn is_pure_state_expr(e: &Ex) -> bool {
    let mut w = Walk { vars: Vec::new(), seen: HashSet::new(), steps: 0 };
    w.node(e)
}

fn bi_pure(b: B) -> bool {
    !matches!(b, B::Prime | B::Enabled | B::Unchanged | B::LeadsTo | B::Always | B::Eventually | B::Cdot | B::TemporalImplies)
}

impl Walk {
    fn def(&mut self, d: &Rc<CompiledDef>) -> bool {
        if d.native.get().is_some() {
            let o = d.src.original();
            return crate::memo::pure_native(&o.module, &o.name);
        }
        if !self.seen.insert(d.id) {
            return true;
        }
        let body = d.body.borrow().clone();
        match body {
            Some(b) => self.node(&b),
            None => false,
        }
    }

    fn arg(&mut self, a: &Arg) -> bool {
        match a {
            Arg::Val(e, _) | Arg::State(e, _) | Arg::ValClosed(e) => self.node(e),
            Arg::Op(OpRef::Def(d)) => self.def(d),
            Arg::Op(OpRef::Builtin(b)) => bi_pure(*b),
            Arg::Op(_) => false,
        }
    }

    fn all(&mut self, es: &[Ex]) -> bool {
        es.iter().all(|x| self.node(x))
    }

    fn bounds(&mut self, bs: &[BoundIr]) -> bool {
        bs.iter().all(|b| self.node(&b.set))
    }

    fn node(&mut self, e: &Ex) -> bool {
        self.steps += 1;
        if self.steps > 100_000 {
            return false;
        }
        match &**e {
            Node::LetRec(defs, body) => defs.iter().all(|(_, l)| self.node(&l.body)) && self.node(body),
            Node::Fold(x, _) => self.node(x),
            Node::Arith(_, a, b, _) => self.node(a) && self.node(b),
            Node::Const(_) | Node::Local(_) => true,
            Node::Var(i) => {
                self.vars.push(*i);
                true
            }
            Node::PrimedVar(_) | Node::Prime(_) | Node::Unchanged(_) => false,
            // a constant declaration: its value is fixed by the configuration or by the INSTANCE substitutions in scope
            // (the cache is only used under the same substitution list); a variable declaration may be substituted
            Node::Decl(dr) => !dr.is_var,
            Node::CallDecl(..) | Node::CallLocal(..) => false,
            Node::Call(d, args, _) => args.iter().all(|a| self.arg(a)) && self.def(d),
            Node::Bi(b, es) => bi_pure(*b) && self.all(es),
            Node::And(es) | Node::Or(es) | Node::Tuple(es) | Node::SetEnum(es) | Node::Times(es) => self.all(es),
            Node::Not(x) => self.node(x),
            Node::Implies(a, b) | Node::Equiv(a, b) | Node::Eq(a, b) | Node::Neq(a, b) | Node::In(a, b) | Node::NotIn(a, b) => {
                self.node(a) && self.node(b)
            }
            Node::FcnApply(a, b) | Node::SetOfFcns(a, b) => self.node(a) && self.node(b),
            Node::Record(x, _) => self.node(x),
            Node::SubsetOf { bound, pred, .. } => self.node(&bound.set) && self.node(pred),
            Node::SetOfAll(x, bs) => self.node(x) && self.bounds(bs),
            Node::FcnCons(bs, body, ..) => self.bounds(bs) && self.node(body),
            Node::RcdCons(fs, ..) | Node::SetOfRcds(fs) => fs.iter().all(|(_, x)| self.node(x)),
            Node::Except(x, specs) => {
                self.node(x)
                    && specs.iter().all(|sp| {
                        sp.path.iter().all(|p| match p {
                            PathIr::Field(_) => true,
                            PathIr::Index(i) => self.node(i),
                        }) && self.node(&sp.val)
                    })
            }
            Node::ActionSub { .. } => false,
            Node::If(c, t, f) => self.node(c) && self.node(t) && self.node(f),
            Node::Case(arms, other) => arms.iter().all(|(c, v)| self.node(c) && self.node(v)) && other.as_ref().map_or(true, |o| self.node(o)),
            Node::Exists(bs, body) | Node::Forall(bs, body) => self.bounds(bs) && self.node(body),
            Node::Choose(b, body) => self.node(&b.set) && self.node(body),
            Node::SubstIn(..) => false,
            Node::Temporal(_) | Node::Unsupported(_) | Node::Fail(_) => false,
            Node::InlineCall { assigns, body } => assigns.iter().all(|(_, a)| self.arg(a)) && self.node(body),
            Node::LetScope(_, body) => self.node(body),
            Node::LetUse(_, def) => self.node(def),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Value;

    fn reads(e: Ex) -> Option<Vec<u32>> {
        let mut w = Walk { vars: Vec::new(), seen: HashSet::new(), steps: 0 };
        if w.node(&e) {
            w.vars.sort_unstable();
            w.vars.dedup();
            Some(w.vars)
        } else {
            None
        }
    }

    fn n(x: Node) -> Ex {
        Rc::new(x)
    }

    #[test]
    fn collects_the_variables_a_definition_reads() {
        // x = 1 /\ (z \in S) /\ x # z   (variables 0 and 2)
        let e = n(Node::And(vec![
            n(Node::Eq(n(Node::Var(0)), n(Node::Const(Value::Int(1))))),
            n(Node::In(n(Node::Var(2)), n(Node::Const(Value::Interval(1, 3))))),
            n(Node::Neq(n(Node::Var(0)), n(Node::Var(2)))),
        ]));
        assert_eq!(reads(e), Some(vec![0, 2]));
        // a constant expression reads nothing
        assert_eq!(reads(n(Node::Const(Value::Int(3)))), Some(vec![]));
    }

    #[test]
    fn rejects_whatever_depends_on_the_next_state_or_the_context() {
        // x' = 1
        assert!(reads(n(Node::Eq(n(Node::PrimedVar(0)), n(Node::Const(Value::Int(1)))))).is_none());
        assert!(reads(n(Node::Prime(n(Node::Var(0))))).is_none());
        assert!(reads(n(Node::Unchanged(n(Node::Var(0))))).is_none());
        // temporal / action-level builtins
        assert!(reads(n(Node::Bi(B::Enabled, vec![n(Node::Var(0))]))).is_none());
        assert!(reads(n(Node::Bi(B::Always, vec![n(Node::Var(0))]))).is_none());
        // operator parameters and INSTANCE substitutions are not analysed
        assert!(reads(n(Node::CallLocal(0, vec![]))).is_none());
        assert!(reads(n(Node::Unsupported("x".into()))).is_none());
        // a pure builtin around a variable is fine
        assert_eq!(reads(n(Node::Bi(B::Domain, vec![n(Node::Var(1))]))), Some(vec![1]));
    }
}

#[cfg(test)]
mod pure_tests {
    use super::*;
    use crate::value::Value;

    #[test]
    fn pure_state_expressions() {
        let c = |v: i32| Rc::new(Node::Const(Value::Int(v)));
        // x + 1 = Local(0) is pure; anything primed is not
        let pure = Rc::new(Node::Eq(Rc::new(Node::Var(0)), Rc::new(Node::Local(0))));
        assert!(is_pure_state_expr(&pure));
        assert!(!is_pure_state_expr(&Rc::new(Node::Eq(Rc::new(Node::PrimedVar(0)), c(1)))));
        assert!(!is_pure_state_expr(&Rc::new(Node::Fail("x".into()))));
    }
}
