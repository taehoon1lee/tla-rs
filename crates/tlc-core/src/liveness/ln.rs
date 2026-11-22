//! Port of `tlc2.tool.liveness.{LiveExprNode, LNBool, LNState, LNStateAST, LNStateEnabled, LNAction, LNNeg, LNConj, LNDisj,
//! LNEven, LNAll, LNNext}`: the temporal formula tree used by the liveness checker, its normalization (push negations,
//! simplify, disjunctive normal form) and evaluation (on a state, on a transition, on a lasso).

use crate::eval::Ev;
use crate::ir::{Ex, Slot};
use crate::value::*;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

/// `LevelConstants`
pub const LEVEL_CONST: u8 = 0;
pub const LEVEL_VAR: u8 = 1;
pub const LEVEL_ACTION: u8 = 2;
pub const LEVEL_TEMPORAL: u8 = 3;

/// `TLCRS_LIVE_DEBUG` (read once: the environment lookup is a system call)
fn debug_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("TLCRS_LIVE_DEBUG").is_ok())
}

/// a compiled expression (or action) together with the values of the enclosing bound variables (Java: `Context`)
pub struct Leaf {
    pub ex: Ex,
    /// subscript of `ENABLED <<A>>_v` (the step must change `v`)
    pub sub: Option<Ex>,
    pub nslots: Rc<Cell<usize>>,
    /// values of the enclosing bound variables: they occupy the first slots of the frame
    pub bound: Vec<Value>,
    pub text: String,
}

impl Leaf {
    fn enter<T>(&self, ev: &Ev, f: impl FnOnce(&Ev) -> R<T>) -> R<T> {
        ev.epoch.set(ev.epoch.get() + 1);
        let r = ev.with_frame(self.nslots.get().max(self.bound.len()), |ev| {
            for (i, v) in self.bound.iter().enumerate() {
                ev.set_slot(i as u32, Slot::V(v.clone()));
            }
            f(ev)
        });
        if let Err(e) = &r {
            if debug_on() {
                eprintln!("liveness leaf failed: {} ({})", self.text, e.msg);
            }
        }
        r
    }

    /// evaluate to a value on the step `s0 -> s1`
    pub fn eval_value(&self, ev: &Ev, s0: &[Value], s1: &[Value]) -> R<Value> {
        self.enter(ev, |ev| ev.eval(&self.ex, s0, s1))
    }

    /// evaluate as a boolean on the step `s0 -> s1`
    pub fn eval_bool(&self, ev: &Ev, s0: &[Value], s1: &[Value], non_bool: i32) -> R<bool> {
        let r = self.enter(ev, |ev| match ev.eval(&self.ex, s0, s1)? {
            Value::Bool(b) => Ok(b),
            _ => fail_code(non_bool, "A temporal formula contains a non-boolean state or action predicate."),
        });
        if r.is_err() && debug_on() {
            eprintln!("liveness leaf failed: {} s0={:?} s1={:?}", self.text, s0, s1);
        }
        r
    }

    /// `ENABLED A` (or `ENABLED <<A>>_v` when there is a subscript) in `s0`
    pub fn eval_enabled(&self, ev: &Ev, s0: &[Value]) -> R<bool> {
        let r = self.enter(ev, |ev| ev.enabled_changed(&self.ex, self.sub.as_ref(), s0));
        if r.is_err() && debug_on() {
            eprintln!("ENABLED failed at s0={:?}", s0);
        }
        r
    }
}

pub struct StateLeaf {
    pub tag: Cell<u32>,
    pub leaf: Leaf,
    /// `LNStateEnabled` (else `LNStateAST`)
    pub enabled: bool,
}

pub struct ActionLeaf {
    pub tag: Cell<u32>,
    pub leaf: Leaf,
}

#[derive(Clone)]
pub struct Ln(pub Rc<LnNode>);

pub enum LnNode {
    Bool(bool),
    State(Rc<StateLeaf>),
    Action(Rc<ActionLeaf>),
    Neg(Ln),
    Conj(Vec<Ln>),
    Disj(Vec<Ln>),
    /// `<>`
    Even(Ln),
    /// `[]`
    All(Ln),
    Next(Ln),
}

use LnNode::*;

/// error codes used by evaluation
pub const EC_NONBOOL_STATE: i32 = crate::ec::TLC_LIVE_STATE_PREDICATE_NON_BOOL;
pub const EC_NONBOOL_ACTION: i32 = crate::ec::TLC_LIVE_ENCOUNTERED_NONBOOL_PREDICATE;

impl Ln {
    pub fn new(n: LnNode) -> Ln {
        Ln(Rc::new(n))
    }
    pub fn bool_(b: bool) -> Ln {
        Ln::new(Bool(b))
    }
    pub fn neg(a: Ln) -> Ln {
        Ln::new(Neg(a))
    }
    pub fn even(a: Ln) -> Ln {
        Ln::new(Even(a))
    }
    pub fn all(a: Ln) -> Ln {
        Ln::new(All(a))
    }
    pub fn next(a: Ln) -> Ln {
        Ln::new(Next(a))
    }
    /// `new LNConj(n1, n2)`: no flattening
    pub fn conj2(a: Ln, b: Ln) -> Ln {
        Ln::new(Conj(vec![a, b]))
    }
    pub fn disj2(a: Ln, b: Ln) -> Ln {
        Ln::new(Disj(vec![a, b]))
    }
    /// `new LNConj(Vect)`: no flattening
    pub fn conj_raw(v: Vec<Ln>) -> Ln {
        Ln::new(Conj(v))
    }
    pub fn disj_raw(v: Vec<Ln>) -> Ln {
        Ln::new(Disj(v))
    }
    /// `LNConj.addConj` semantics: nested conjunctions are flattened
    pub fn conj_flat(items: impl IntoIterator<Item = Ln>) -> Ln {
        let mut out = vec![];
        for it in items {
            add_conj(&mut out, it);
        }
        Ln::new(Conj(out))
    }
    pub fn disj_flat(items: impl IntoIterator<Item = Ln>) -> Ln {
        let mut out = vec![];
        for it in items {
            add_disj(&mut out, it);
        }
        Ln::new(Disj(out))
    }

    pub fn is_state(&self) -> bool {
        matches!(&*self.0, State(_))
    }
    pub fn is_action(&self) -> bool {
        matches!(&*self.0, Action(_))
    }
    pub fn is_bool(&self) -> bool {
        matches!(&*self.0, Bool(_))
    }

    /// `getLevel`
    pub fn level(&self) -> u8 {
        match &*self.0 {
            Bool(_) => LEVEL_CONST,
            State(_) => LEVEL_VAR,
            Action(_) => LEVEL_ACTION,
            Neg(b) => b.level(),
            Conj(v) | Disj(v) => v.iter().map(|x| x.level()).max().unwrap_or(0),
            Even(_) | All(_) => LEVEL_TEMPORAL,
            Next(_) => LEVEL_ACTION,
        }
    }

    /// `containAction`
    pub fn contains_action(&self) -> bool {
        match &*self.0 {
            Bool(_) | State(_) => false,
            Action(_) => true,
            Neg(b) | Even(b) | All(b) | Next(b) => b.contains_action(),
            Conj(v) | Disj(v) => v.iter().any(|x| x.contains_action()),
        }
    }

    /// `isPositiveForm`
    pub fn is_positive_form(&self) -> bool {
        match &*self.0 {
            Neg(b) => b.is_bool() || b.is_state(),
            Conj(v) | Disj(v) => v.iter().all(|x| x.is_positive_form()),
            Even(b) | All(b) | Next(b) => b.is_positive_form(),
            _ => true,
        }
    }

    /// `equals` (state and action predicates are compared by their tags)
    pub fn equals(&self, o: &Ln) -> bool {
        match (&*self.0, &*o.0) {
            (Bool(a), Bool(b)) => a == b,
            (State(a), State(b)) => a.tag.get() == b.tag.get(),
            (Action(a), Action(b)) => a.tag.get() == b.tag.get(),
            (Neg(a), Neg(b)) | (Even(a), Even(b)) | (All(a), All(b)) | (Next(a), Next(b)) => a.equals(b),
            (Conj(a), Conj(b)) | (Disj(a), Disj(b)) => a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.equals(y)),
            _ => false,
        }
    }

    /// `getAEBody`: `[]<>b` -> `b`
    pub fn ae_body(&self) -> Option<Ln> {
        if let All(b) = &*self.0 {
            if let Even(c) = &*b.0 {
                return Some(c.clone());
            }
        }
        None
    }

    /// `tagExpr`
    pub fn tag_expr(&self, tag: u32) -> u32 {
        match &*self.0 {
            Bool(_) => tag,
            State(s) => {
                s.tag.set(tag);
                tag + 1
            }
            Action(a) => {
                a.tag.set(tag);
                tag + 1
            }
            Neg(b) | Even(b) | All(b) | Next(b) => b.tag_expr(tag),
            Conj(v) | Disj(v) => {
                let mut t = tag;
                for x in v {
                    t = x.tag_expr(t);
                }
                t
            }
        }
    }

    /// `pushNeg()`
    pub fn push_neg(&self) -> Ln {
        match &*self.0 {
            Bool(b) => Ln::bool_(!*b),
            Neg(b) => b.clone(),
            Conj(v) => Ln::disj_flat(v.iter().map(|x| x.push_neg())),
            Disj(v) => Ln::conj_flat(v.iter().map(|x| x.push_neg())),
            Even(b) => Ln::all(b.push_neg()),
            All(b) => Ln::even(b.push_neg()),
            _ => Ln::neg(self.clone()),
        }
    }

    /// `pushNeg(boolean hasNeg)`
    pub fn push_neg_b(&self, has_neg: bool) -> Ln {
        match &*self.0 {
            Bool(b) => {
                if has_neg {
                    Ln::bool_(!*b)
                } else {
                    self.clone()
                }
            }
            Neg(b) => b.push_neg_b(!has_neg),
            Conj(v) => {
                if has_neg {
                    Ln::disj_flat(v.iter().map(|x| x.push_neg_b(true)))
                } else {
                    Ln::conj_flat(v.iter().map(|x| x.push_neg_b(false)))
                }
            }
            Disj(v) => {
                if has_neg {
                    Ln::conj_flat(v.iter().map(|x| x.push_neg_b(true)))
                } else {
                    Ln::disj_flat(v.iter().map(|x| x.push_neg_b(false)))
                }
            }
            Even(b) => {
                if has_neg {
                    Ln::all(b.push_neg_b(true))
                } else {
                    Ln::even(b.push_neg_b(false))
                }
            }
            All(b) => {
                if has_neg {
                    Ln::even(b.push_neg_b(true))
                } else {
                    Ln::all(b.push_neg_b(false))
                }
            }
            _ => {
                if has_neg {
                    Ln::neg(self.clone())
                } else {
                    self.clone()
                }
            }
        }
    }

    /// `simplify`
    pub fn simplify(&self) -> Ln {
        match &*self.0 {
            Neg(b) => {
                let b1 = b.simplify();
                if let Bool(x) = &*b1.0 {
                    Ln::bool_(!*x)
                } else {
                    Ln::neg(b1)
                }
            }
            Conj(v) => {
                let mut out = vec![];
                for x in v {
                    let e = x.simplify();
                    if let Bool(b) = &*e.0 {
                        if !*b {
                            return Ln::bool_(false);
                        }
                    } else {
                        add_conj(&mut out, e);
                    }
                }
                match out.len() {
                    0 => Ln::bool_(true),
                    1 => out.pop().unwrap(),
                    _ => Ln::new(Conj(out)),
                }
            }
            Disj(v) => {
                let mut out = vec![];
                for x in v {
                    let e = x.simplify();
                    if let Bool(b) = &*e.0 {
                        if *b {
                            return Ln::bool_(true);
                        }
                    } else {
                        add_disj(&mut out, e);
                    }
                }
                match out.len() {
                    0 => Ln::bool_(false),
                    1 => out.pop().unwrap(),
                    _ => Ln::new(Disj(out)),
                }
            }
            Even(b) => {
                let mut b1 = b.simplify();
                if let Even(c) = &*b1.0 {
                    b1 = c.clone();
                }
                Ln::even(b1)
            }
            All(b) => {
                let mut b1 = b.simplify();
                if let All(c) = &*b1.0 {
                    b1 = c.clone();
                }
                Ln::all(b1)
            }
            _ => self.clone(),
        }
    }

    /// `toDNF`; `Err` = the formula exceeds the maximum size in disjunctive normal form
    pub fn to_dnf(&self) -> Result<Ln, ()> {
        Ok(match &*self.0 {
            Neg(b) => {
                if b.is_state() || b.is_action() {
                    self.clone()
                } else {
                    b.push_neg().to_dnf()?
                }
            }
            Disj(v) => {
                let mut ae_res: Vec<Ln> = vec![];
                let mut res: Vec<Ln> = vec![];
                for x in v {
                    let elem = x.to_dnf()?;
                    if let Disj(inner) = &*elem.0 {
                        for e1 in inner {
                            match e1.ae_body() {
                                None => add_disj(&mut res, e1.clone()),
                                Some(b) => add_disj(&mut ae_res, b),
                            }
                        }
                    } else {
                        match elem.ae_body() {
                            None => add_disj(&mut res, elem),
                            Some(b) => add_disj(&mut ae_res, b),
                        }
                    }
                }
                if ae_res.len() == 1 {
                    add_disj(&mut res, Ln::all(Ln::even(ae_res.pop().unwrap())));
                } else if ae_res.len() > 1 {
                    add_disj(&mut res, Ln::all(Ln::even(Ln::new(Disj(ae_res)))));
                }
                Ln::new(Disj(res))
            }
            Conj(v) => {
                let count = v.len();
                let mut temp = Vec::with_capacity(count);
                for x in v {
                    temp.push(x.to_dnf()?);
                }
                let mut nes: Vec<Ln> = Vec::with_capacity(count);
                let mut total: usize = 1;
                for elem in temp {
                    match &*elem.0 {
                        Disj(d) => {
                            total = total.checked_mul(d.len()).ok_or(())?;
                            nes.push(elem.clone());
                        }
                        Conj(c) => {
                            for y in c {
                                nes.push(y.clone());
                            }
                        }
                        _ => nes.push(elem),
                    }
                }
                if total == 1 {
                    return Ok(Ln::new(Conj(nes)));
                }
                if total > 50_000_000 {
                    return Err(());
                }
                let nes_size = nes.len();
                let mut res: Vec<Vec<Ln>> = (0..total).map(|_| Vec::with_capacity(nes_size)).collect();
                let mut num = 1usize;
                let mut r_count = total;
                for ln in &nes {
                    if let Disj(disj) = &*ln.0 {
                        r_count /= disj.len();
                        let mut idx = 0usize;
                        for _ in 0..num {
                            for elem in disj.iter() {
                                for _ in 0..r_count {
                                    add_conj(&mut res[idx], elem.clone());
                                    idx += 1;
                                }
                            }
                        }
                        num *= disj.len();
                    } else {
                        for r in res.iter_mut() {
                            add_conj(r, ln.clone());
                        }
                    }
                }
                Ln::new(Disj(res.into_iter().map(|c| Ln::new(Conj(c))).collect()))
            }
            _ => self.clone(),
        })
    }

    /// `flattenSingleJunctions`
    pub fn flatten_single(&self) -> Ln {
        match &*self.0 {
            Neg(b) => {
                if let Neg(c) = &*b.0 {
                    c.flatten_single()
                } else {
                    Ln::neg(b.flatten_single())
                }
            }
            Conj(v) => {
                if v.len() == 1 {
                    return v[0].flatten_single();
                }
                let mut out = vec![];
                for x in v {
                    add_conj(&mut out, x.flatten_single());
                }
                Ln::new(Conj(out))
            }
            Disj(v) => {
                if v.len() == 1 {
                    return v[0].flatten_single();
                }
                let mut out = vec![];
                for x in v {
                    add_disj(&mut out, x.flatten_single());
                }
                Ln::new(Disj(out))
            }
            Even(b) => Ln::even(b.flatten_single()),
            All(b) => Ln::all(b.flatten_single()),
            Next(b) => Ln::next(b.flatten_single()),
            _ => self.clone(),
        }
    }

    /// `makeBinary`: conjunctions/disjunctions have at most two operands
    pub fn make_binary(&self) -> Ln {
        match &*self.0 {
            Neg(b) => Ln::neg(b.make_binary()),
            Even(b) => Ln::even(b.make_binary()),
            All(b) => Ln::all(b.make_binary()),
            Next(b) => Ln::next(b.make_binary()),
            Conj(v) => {
                if v.len() == 1 {
                    return v[0].make_binary();
                }
                let mid = v.len() / 2;
                let left = Ln::conj_flat(v[..mid].iter().cloned());
                let right = Ln::conj_flat(v[mid..].iter().cloned());
                Ln::conj2(left.make_binary(), right.make_binary())
            }
            Disj(v) => {
                if v.len() == 1 {
                    return v[0].make_binary();
                }
                let mid = v.len() / 2;
                let left = Ln::disj_flat(v[..mid].iter().cloned());
                let right = Ln::disj_flat(v[mid..].iter().cloned());
                Ln::disj2(left.make_binary(), right.make_binary())
            }
            _ => self.clone(),
        }
    }

    /// `extractPromises`: every `<>f` subformula, once
    pub fn extract_promises(&self, out: &mut Vec<Ln>) {
        match &*self.0 {
            Neg(b) | All(b) | Next(b) => b.extract_promises(out),
            Even(b) => {
                if !out.iter().any(|p| p.equals(self)) {
                    out.push(self.clone());
                }
                b.extract_promises(out);
            }
            Conj(v) | Disj(v) => {
                v[0].extract_promises(out);
                v[1].extract_promises(out);
            }
            _ => {}
        }
    }

    // ------------------------------------------------------------------ evaluation

    /// `eval(tool, s1, s2)`: state predicates read `s1`, action predicates `s1 -> s2`
    pub fn eval(&self, ev: &Ev, s1: &[Value], s2: &[Value]) -> R<bool> {
        match &*self.0 {
            Bool(b) => Ok(*b),
            State(s) => {
                if s.enabled {
                    s.leaf.eval_enabled(ev, s1)
                } else {
                    s.leaf.eval_bool(ev, s1, &ev.empty(), EC_NONBOOL_STATE)
                }
            }
            Action(a) => a.leaf.eval_bool(ev, s1, s2, EC_NONBOOL_ACTION),
            Neg(b) => Ok(!b.eval(ev, s1, s2)?),
            Conj(v) => {
                for x in v {
                    if !x.eval(ev, s1, s2)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Disj(v) => {
                for x in v {
                    if x.eval(ev, s1, s2)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Next(b) => b.eval(ev, s2, &ev.empty()),
            Even(_) => fail_code(crate::ec::TLC_LIVE_CANNOT_EVAL_FORMULA, "TLC cannot evaluate the temporal formula <> on a state or transition."),
            All(_) => fail_code(crate::ec::TLC_LIVE_CANNOT_EVAL_FORMULA, "TLC cannot evaluate the temporal formula [] on a state or transition."),
        }
    }

    /// `evalOnLasso`: the behavior `states[0] .. states[n-1]` followed by `states[cycle_pos]` forever
    pub fn eval_on_lasso(&self, ev: &Ev, states: &[Vec<Value>], cycle_pos: usize, pos: usize) -> R<bool> {
        match &*self.0 {
            Bool(b) => Ok(*b),
            State(s) => {
                if s.enabled {
                    s.leaf.eval_enabled(ev, &states[pos])
                } else {
                    s.leaf.eval_bool(ev, &states[pos], &ev.empty(), EC_NONBOOL_STATE)
                }
            }
            Action(a) => {
                let s2 = if pos + 1 < states.len() { &states[pos + 1] } else { &states[cycle_pos] };
                a.leaf.eval_bool(ev, &states[pos], s2, EC_NONBOOL_ACTION)
            }
            Neg(b) => Ok(!b.eval_on_lasso(ev, states, cycle_pos, pos)?),
            Conj(v) => {
                for x in v {
                    if !x.eval_on_lasso(ev, states, cycle_pos, pos)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Disj(v) => {
                for x in v {
                    if x.eval_on_lasso(ev, states, cycle_pos, pos)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Next(b) => {
                let next = if pos + 1 < states.len() { pos + 1 } else { cycle_pos };
                b.eval_on_lasso(ev, states, cycle_pos, next)
            }
            Even(b) => {
                if pos < cycle_pos {
                    for i in pos..cycle_pos {
                        if b.eval_on_lasso(ev, states, cycle_pos, i)? {
                            return Ok(true);
                        }
                    }
                }
                for i in cycle_pos..states.len() {
                    if b.eval_on_lasso(ev, states, cycle_pos, i)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            All(b) => {
                if pos < cycle_pos {
                    for i in pos..cycle_pos {
                        if !b.eval_on_lasso(ev, states, cycle_pos, i)? {
                            return Ok(false);
                        }
                    }
                }
                for i in cycle_pos..states.len() {
                    if !b.eval_on_lasso(ev, states, cycle_pos, i)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }

    /// a short rendering for diagnostics
    pub fn render(&self) -> String {
        match &*self.0 {
            Bool(b) => if *b { "TRUE".into() } else { "FALSE".into() },
            State(s) => if s.enabled { format!("ENABLED {}", s.leaf.text) } else { s.leaf.text.clone() },
            Action(a) => a.leaf.text.clone(),
            Neg(b) => format!("-{}", b.render()),
            Conj(v) => v.iter().map(|x| format!("/\\ ({})", x.render())).collect::<Vec<_>>().join("\n"),
            Disj(v) => v.iter().map(|x| format!("\\/ ({})", x.render())).collect::<Vec<_>>().join("\n"),
            Even(b) => format!("<>({})", b.render()),
            All(b) => format!("[]({})", b.render()),
            Next(b) => format!("(){}", b.render()),
        }
    }
}

/// `LNConj.addConj`
pub fn add_conj(out: &mut Vec<Ln>, elem: Ln) {
    if let Conj(v) = &*elem.0 {
        for x in v {
            add_conj(out, x.clone());
        }
    } else {
        out.push(elem);
    }
}

/// `LNDisj.addDisj`
pub fn add_disj(out: &mut Vec<Ln>, elem: Ln) {
    if let Disj(v) = &*elem.0 {
        for x in v {
            add_disj(out, x.clone());
        }
    } else {
        out.push(elem);
    }
}

#[allow(dead_code)]
fn _unused(_: &RefCell<u8>) {}

#[cfg(test)]
mod tests {
    use super::*;

    fn b(x: bool) -> Ln {
        Ln::bool_(x)
    }

    #[test]
    fn simplify_constants() {
        assert!(matches!(&*Ln::neg(b(true)).simplify().0, LnNode::Bool(false)));
        let c = Ln::conj_flat(vec![b(true), b(true)]);
        assert!(matches!(&*c.simplify().0, LnNode::Bool(true)));
        let d = Ln::disj_flat(vec![b(false), b(true)]);
        assert!(matches!(&*d.simplify().0, LnNode::Bool(true)));
    }

    #[test]
    fn push_neg_swaps_temporal_operators() {
        // ~[]<>p  ==  <>[]~p
        let f = Ln::neg(Ln::all(Ln::even(b(true)))).push_neg_b(false);
        match &*f.0 {
            LnNode::Even(x) => assert!(matches!(&*x.0, LnNode::All(_))),
            _ => panic!("expected <>[]"),
        }
    }

    #[test]
    fn dnf_distributes_conjunction_over_disjunction() {
        // (a \/ b) /\ c  ->  (a /\ c) \/ (b /\ c)   (leaves are constants here, only the shape is checked)
        let f = Ln::conj_raw(vec![Ln::disj_raw(vec![b(true), b(false)]), b(true)]);
        match &*f.to_dnf().unwrap().0 {
            LnNode::Disj(v) => {
                assert_eq!(v.len(), 2);
                assert!(v.iter().all(|x| matches!(&*x.0, LnNode::Conj(c) if c.len() == 2)));
            }
            _ => panic!("expected a disjunction"),
        }
    }

    #[test]
    fn make_binary_splits_conjunctions() {
        let f = Ln::conj_flat(vec![b(true), b(false), b(true), b(false)]).make_binary();
        match &*f.0 {
            LnNode::Conj(v) => assert_eq!(v.len(), 2),
            _ => panic!("expected a binary conjunction"),
        }
    }

    #[test]
    fn levels() {
        assert_eq!(Ln::all(b(true)).level(), LEVEL_TEMPORAL);
        assert_eq!(Ln::next(b(true)).level(), LEVEL_ACTION);
        assert_eq!(b(true).level(), LEVEL_CONST);
    }
}
