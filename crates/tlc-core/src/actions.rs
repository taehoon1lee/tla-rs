//! Port of the state generation of `tlc2.tool.impl.Tool`: `getInitStates` / `getNextStates` — the evaluation of an
//! action formula that *enumerates* the ways to assign the (primed) variables, instead of just computing a boolean.
//!
//! The partially assigned successor (or initial) state lives in a `RefCell<Vec<Value>>` (`Undef` = unassigned) so
//! that guards can be evaluated while the continuation keeps assigning.

use crate::eval::*;
use crate::ir::*;
use crate::value::*;
use std::cell::RefCell;
use std::rc::Rc;
use tla_sany::sem::B;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Init,
    Next,
}

pub type Buf = RefCell<Vec<Value>>;
pub type Cont<'a> = dyn FnMut() -> R<()> + 'a;

/// a state-level expression that reads state variables, parameters and constants only (no primes, no by-name arguments)
fn plain_test_expr(e: &Ex) -> bool {
    match &**e {
        Node::Const(_) | Node::Var(_) | Node::Local(_) => true,
        Node::Eq(a, b) | Node::Neq(a, b) | Node::In(a, b) | Node::NotIn(a, b) | Node::FcnApply(a, b) | Node::Implies(a, b) | Node::Equiv(a, b) => {
            plain_test_expr(a) && plain_test_expr(b)
        }
        Node::Arith(_, a, b, _) => plain_test_expr(a) && plain_test_expr(b),
        Node::Not(x) | Node::Record(x, _) => plain_test_expr(x),
        Node::And(es) | Node::Or(es) | Node::Tuple(es) | Node::SetEnum(es) => es.iter().all(plain_test_expr),
        Node::Bi(b, es) => {
            !matches!(
                b,
                tla_sany::sem::B::Prime
                    | tla_sany::sem::B::Enabled
                    | tla_sany::sem::B::Unchanged
                    | tla_sany::sem::B::LeadsTo
                    | tla_sany::sem::B::Always
                    | tla_sany::sem::B::Eventually
                    | tla_sany::sem::B::Cdot
                    | tla_sany::sem::B::TemporalImplies
            ) && es.iter().all(plain_test_expr)
        }
        // a call of a native or of a state-level definition with plain arguments
        Node::Call(d, args, _) => {
            (d.native.get().is_some() || d.level <= tla_sany::sem::Level::State)
                && args.iter().all(|a| match a {
                    Arg::Val(x, false) => plain_test_expr(x),
                    _ => false,
                })
        }
        _ => false,
    }
}

/// `Some(test)` when the body of `d` is `/\ test /\ ...` and `test` is a comparison / membership test over plain
/// state-level operands: it can be evaluated right after the frame of a call is set up (see `enum_def_call`)
fn first_test(d: &Rc<CompiledDef>) -> Option<Ex> {
    d.first_test
        .get_or_init(|| {
            let body = d.body.borrow().clone()?;
            match &*body {
                Node::And(items) if items.len() >= 2 => {
                    let t = &items[0];
                    match &**t {
                        Node::Eq(..) | Node::Neq(..) | Node::In(..) | Node::NotIn(..) if plain_test_expr(t) => Some(t.clone()),
                        _ => None,
                    }
                }
                _ => None,
            }
        })
        .clone()
}

fn body_loc(d: &tla_sany::sem::OpDef) -> tla_sany::ast::Loc {
    match d.body() {
        Some(b) => b.loc,
        None => d.loc,
    }
}

impl Ev {
    fn guard(&self, ex: &Ex, mode: Mode, s0: &[Value], buf: &Buf) -> R<Value> {
        let b = buf.borrow();
        match mode {
            Mode::Init => {
                let empty = self.empty();
                self.eval(ex, &b, &empty)
            }
            Mode::Next => self.eval(ex, s0, &b),
        }
    }

    fn eval_expr(&self, ex: &Ex, mode: Mode, s0: &[Value], buf: &Buf) -> R<Value> {
        self.guard(ex, mode, s0, buf)
    }

    fn target_var(&self, ex: &Ex, mode: Mode) -> Option<u32> {
        match (&**ex, mode) {
            (Node::PrimedVar(i, _), Mode::Next) => Some(*i),
            // Java: getPrimedVar follows definitions without parameters (`F == x'`)
            (Node::Call(d, args, _), Mode::Next) if args.is_empty() && d.native.get().is_none() && d.level >= tla_sany::sem::Level::Action => {
                let body = d.body.borrow().clone();
                match body {
                    Some(b) => self.target_var(&b, mode),
                    None => None,
                }
            }
            // Java: getPrimedVar follows a SubstInNode (`I!F` with `x <- a` where `F == x'`): the substitutions are in scope
            // for the body.  Only substitutions that need no state to be captured (lazy / closed arguments) are followed.
            (Node::SubstIn(subs, body, _, _), _) => {
                let outer = self.substs.borrow().clone();
                let mut cur = outer.clone();
                let empty = self.empty();
                for (decl, a) in subs {
                    if !matches!(a, Arg::State(..) | Arg::ValClosed(_)) {
                        return None;
                    }
                    let slot = self.eval_arg_pub(a, &empty, &empty).ok()?;
                    cur = cur.push(SubstEntry { decl: *decl, slot });
                }
                *self.substs.borrow_mut() = cur;
                let r = self.target_var(body, mode);
                *self.substs.borrow_mut() = outer;
                r
            }
            // a parameter bound (by name) to a primed variable, e.g. `Send(p, d, memInt, memInt')`: `new = ...`
            (Node::Local(s), Mode::Init) => match self.get_slot(*s) {
                Slot::Lazy(l) => self.code_target(&l.code, &l.substs),
                _ => None,
            },
            (Node::Local(s), Mode::Next) => match self.get_slot(*s) {
                Slot::Lazy(l) => match &*l.code {
                    Node::PrimedVar(i, _) => Some(*i),
                    Node::Prime(inner) => match &**inner {
                        Node::Decl(dr) if dr.is_var => self.decl_target(dr.id, dr.is_var, dr.var_index, &l.substs),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            },
            (Node::Var(i), Mode::Init) => Some(*i),
            (Node::Decl(dr), Mode::Init) if dr.is_var => self.decl_target(dr.id, dr.is_var, dr.var_index, &self.substs.borrow()),
            (Node::Prime(inner), Mode::Next) => match &**inner {
                Node::Decl(dr) if dr.is_var => self.decl_target(dr.id, dr.is_var, dr.var_index, &self.substs.borrow()),
                // a parameter bound (by name) to a state variable: `q'` with `Lose(msgQ)`
                Node::Local(s) => match self.get_slot(*s) {
                    Slot::Lazy(l) => self.code_target(&l.code, &l.substs),
                    _ => None,
                },
                // Java: getVar follows definitions without parameters and SubstInNodes: `(I!F)'` with `F == x`
                Node::Call(..) | Node::SubstIn(..) => self.var_of(inner),
                _ => None,
            },
            _ => None,
        }
    }

    /// Java: `SymbolNodeValueLookupProvider.getVar`: the state variable `ex` stands for, looking through definitions without
    /// parameters and INSTANCE substitutions
    fn var_of(&self, ex: &Ex) -> Option<u32> {
        match &**ex {
            Node::Var(i) => Some(*i),
            Node::Decl(dr) => self.decl_target(dr.id, dr.is_var, dr.var_index, &self.substs.borrow()),
            Node::Call(d, args, _) if args.is_empty() && d.native.get().is_none() => {
                let body = d.body.borrow().clone();
                body.and_then(|b| self.var_of(&b))
            }
            Node::SubstIn(subs, body, _, _) => {
                let outer = self.substs.borrow().clone();
                let mut cur = outer.clone();
                let empty = self.empty();
                for (decl, a) in subs {
                    if !matches!(a, Arg::State(..) | Arg::ValClosed(_)) {
                        return None;
                    }
                    let slot = self.eval_arg_pub(a, &empty, &empty).ok()?;
                    cur = cur.push(SubstEntry { decl: *decl, slot });
                }
                *self.substs.borrow_mut() = cur;
                let r = self.var_of(body);
                *self.substs.borrow_mut() = outer;
                r
            }
            Node::Local(s) => match self.get_slot(*s) {
                Slot::Lazy(l) => self.code_target(&l.code, &l.substs),
                _ => None,
            },
            _ => None,
        }
    }

    /// the state variable a (possibly substituted) variable declaration stands for
    fn decl_target(&self, id: usize, is_var: bool, var_index: u32, substs: &Substs) -> Option<u32> {
        for ent in substs.iter() {
            if ent.decl == id {
                return match &ent.slot {
                    Slot::Lazy(l) => self.code_target(&l.code, &l.substs),
                    _ => None,
                };
            }
        }
        if is_var && var_index != u32::MAX {
            Some(var_index)
        } else {
            None
        }
    }

    fn code_target(&self, code: &Ex, substs: &Substs) -> Option<u32> {
        match &**code {
            Node::Var(i) => Some(*i),
            Node::Decl(dr) => self.decl_target(dr.id, dr.is_var, dr.var_index, substs),
            _ => None,
        }
    }

    /// assign variable `i := v` (or check equality if already assigned) and continue
    fn assign_and_continue(&self, i: u32, v: Value, mode: Mode, buf: &Buf, k: &mut Cont) -> R<()> {
        let cur = buf.borrow()[i as usize].clone();
        match cur {
            Value::Undef => {
                self.epoch.set(self.epoch.get() + 1);
                // Java binds the value as it is; it is normalized (enumerated) when it is fingerprinted or printed.  A power set
                // too big to enumerate stays lazy here so that the failure happens where Java's does (the fingerprint).
                // The same holds for a set enumeration whose elements cannot be compared (`{1, "a"}`).
                let nv = if v.is_huge_subset() {
                    v
                } else {
                    match v.normalize() {
                        Ok(n) => n,
                        Err(_) if v.contains_setu() => v,
                        Err(e) => return Err(e),
                    }
                };
                buf.borrow_mut()[i as usize] = nv;
                let was = self.eval_only.get();
                if !was && (mode == Mode::Init || self.warn.get()) && buf.borrow().iter().all(|x| !matches!(x, Value::Undef)) {
                    // Java: getNextStates0 -> getNextStatesAllAssigned / getInitStates(acts, ps, ..) with `ps.allAssigned()`
                    self.eval_only.set(true);
                }
                let r = k();
                self.eval_only.set(was);
                self.epoch.set(self.epoch.get() + 1);
                buf.borrow_mut()[i as usize] = Value::Undef;
                r
            }
            old => {
                if old.eq_val(&v)? {
                    k()
                } else {
                    Ok(())
                }
            }
        }
    }

    /// enumerate the ways of satisfying `ex`; for each, call `k` with the assignments in `buf`
    pub fn enum_action(&self, ex: &Ex, mode: Mode, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        // Java: `CallStackTool.getInitStates` / `getNextStates`: the node being decomposed is on the stack of an error that leaves it
        match self.enum_action_frames(ex, mode, s0, buf, k) {
            Err(mut e) => {
                e.frames.push(Rc::as_ptr(ex) as usize);
                Err(e)
            }
            ok => ok,
        }
    }

    fn enum_action_frames(&self, ex: &Ex, mode: Mode, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        if self.splitting.get() && !self.eval_only.get() {
            // Java: Tool.getActions: the next-state relation is split at disjunctions, `\E` over constant sets and
            // applications of operators to constant arguments; the first other expression is the action's `pred`
            let splittable = match &**ex {
                Node::Or(_) => true,
                // a LET scope only memoizes definitions: the action is split inside its body
                Node::LetScope(..) => true,
                Node::Exists(..) => self.info_const_sub(ex),
                Node::Call(d, ..) => d.native.get().is_none() && d.body.borrow().is_some() && !d.src.in_let.get() && self.info_const_sub(ex),
                _ => false,
            };
            if !splittable {
                let name = match &**ex {
                    Node::Call(d, ..) => Some(d.name.clone()),
                    _ => None,
                };
                self.set_stop(ex, name);
                self.splitting.set(false);
                let r = self.enum_action_inner(ex, mode, s0, buf, k);
                self.splitting.set(true);
                return r;
            }
        }
        self.enum_action_inner(ex, mode, s0, buf, k)
    }

    fn info_const_sub(&self, ex: &Ex) -> bool {
        self.node_info.borrow().get(&(Rc::as_ptr(ex) as usize)).map_or(false, |i| i.const_sub)
    }

    fn set_stop(&self, ex: &Ex, name: Option<tla_sany::sem::Name>) {
        let mut cl = self.cur_label.borrow_mut();
        if let Some(l) = cl.as_mut() {
            l.stop = Rc::as_ptr(ex) as usize;
            if let Some(nm) = name {
                l.base = Rc::new(LabelBase { name: nm, params: vec![], pnames: vec![] });
            }
        }
    }

    fn enum_action_inner(&self, ex: &Ex, mode: Mode, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        if self.eval_only.get() {
            // Java: getNextStatesAllAssigned: all variables are assigned; the remaining conjuncts are plain predicates
            return match self.guard(ex, mode, s0, buf)? {
                Value::Bool(true) => k(),
                Value::Bool(false) => Ok(()),
                other => fail(format!(
                    "The expression of an action or initial predicate evaluated to the non-boolean value
{}",
                    other.to_tla()
                )),
            };
        }
        match &**ex {
            Node::And(items) => {
                let was = self.splitting.replace(false);
                let r = self.enum_conj(items, 0, mode, s0, buf, k);
                self.splitting.set(was);
                r
            }
            Node::Or(items) => {
                if self.splitting.get() {
                    let saved = self.cur_label.borrow().clone();
                    for it in items {
                        *self.cur_label.borrow_mut() = saved.clone();
                        self.enum_action(it, mode, s0, buf, k)?;
                    }
                    *self.cur_label.borrow_mut() = saved;
                } else {
                    for it in items {
                        self.enum_action(it, mode, s0, buf, k)?;
                    }
                }
                Ok(())
            }
            Node::Eq(l, r) => {
                if let Some(i) = self.target_var(l, mode) {
                    let v = self.eval_expr(r, mode, s0, buf)?;
                    return self.assign_and_continue(i, v, mode, buf, k);
                }
                if let Some(i) = self.target_var(r, mode) {
                    // `e = x'`: TLC evaluates the equality; assign when the variable is still unassigned
                    let unassigned = matches!(buf.borrow()[i as usize], Value::Undef);
                    if unassigned {
                        let v = self.eval_expr(l, mode, s0, buf)?;
                        return self.assign_and_continue(i, v, mode, buf, k);
                    }
                }
                // inside ENABLED: `v' = e` with `v` an INSTANCE-substituted declaration binds `v` by name
                if self.enabled_depth.get() > 0 && mode == Mode::Next {
                    if let Node::Prime(inner) = &**l {
                        if let Node::Decl(dr) = &**inner {
                            if self.substs.borrow().find(dr.id).is_some() {
                                let v = self.eval_expr(r, mode, s0, buf)?;
                                let existing = self.virt.borrow().iter().find(|(id, _)| *id == dr.id).map(|(_, x)| x.clone());
                                return match existing {
                                    Some(old) => {
                                        if old.eq_val(&v)? {
                                            k()
                                        } else {
                                            Ok(())
                                        }
                                    }
                                    None => {
                                        self.virt.borrow_mut().push((dr.id, v));
                                        let res = k();
                                        self.virt.borrow_mut().pop();
                                        res
                                    }
                                };
                            }
                        }
                    }
                }
                if self.guard(ex, mode, s0, buf)?.as_bool()? {
                    k()
                } else {
                    Ok(())
                }
            }
            Node::In(l, set) => {
                if let Some(i) = self.target_var(l, mode) {
                    let unassigned = matches!(buf.borrow()[i as usize], Value::Undef);
                    let sv = self.eval_expr(set, mode, s0, buf)?;
                    if unassigned {
                        if !sv.is_set_like() {
                            return fail(format!(
                                "Attempted to enumerate the elements of the non-set value\n{}\nwhile computing the next state.",
                                sv.to_tla()
                            ));
                        }
                        if let Value::Interval(lo, hi) = &sv {
                            let mut x = *lo;
                            while x <= *hi {
                                self.assign_and_continue(i, Value::Int(x), mode, buf, k)?;
                                if x == i32::MAX {
                                    break;
                                }
                                x += 1;
                            }
                            return Ok(());
                        }
                        let elems = sv.enumerate()?;
                        for e in elems.iter() {
                            self.assign_and_continue(i, e.clone(), mode, buf, k)?;
                        }
                        return Ok(());
                    }
                    let cur = buf.borrow()[i as usize].clone();
                    return if sv.member(&cur)? { k() } else { Ok(()) };
                }
                if self.guard(ex, mode, s0, buf)?.as_bool()? {
                    k()
                } else {
                    Ok(())
                }
            }
            Node::Unchanged(inner) if mode == Mode::Next => {
                let mut vars = vec![];
                if self.unchanged_vars(inner, &mut vars) {
                    // Java: `CallStackTool.processUnchanged`: the operand is on the stack while the rest of the action is enumerated
                    return self.assign_unchanged(&vars, 0, s0, buf, k).map_err(|mut e| {
                        e.frames.push(Rc::as_ptr(inner) as usize);
                        e
                    });
                }
                // inside ENABLED: INSTANCE-substituted declarations are bound by name (Java: `enabledUnchanged`)
                if self.enabled_depth.get() > 0 {
                    let mut elems: Vec<Ex> = vec![];
                    if self.unchanged_elems_of(inner, &mut elems, 0) {
                        return self.unchanged_elems(&elems, 0, s0, buf, k);
                    }
                }
                // Java: processUnchangedImplTuple: tuple elements are processed one by one; the elements that are
                // not variables are only verified (their value must be the same in both states)
                if let Node::Tuple(es) = &**inner {
                    return self.unchanged_tuple(es, 0, s0, buf, k);
                }
                if self.guard(ex, mode, s0, buf)?.as_bool()? {
                    k()
                } else {
                    Ok(())
                }
            }
            Node::ActionSub { boxed: true, act, sub } if mode == Mode::Next => {
                // [A]_v  ==  A \/ UNCHANGED v
                self.enum_action(act, mode, s0, buf, k)?;
                let mut vars = vec![];
                if self.unchanged_vars(sub, &mut vars) {
                    self.assign_unchanged(&vars, 0, s0, buf, k)
                } else {
                    // general subscript: v' = v
                    let cur = self.eval(sub, s0, &s0.to_vec())?;
                    let nxt = {
                        let b = buf.borrow();
                        let empty = self.empty();
                        self.eval(sub, &b, &empty)
                    };
                    match nxt {
                        Ok(n) => {
                            if cur.eq_val(&n)? {
                                k()
                            } else {
                                Ok(())
                            }
                        }
                        Err(e) => Err(e),
                    }
                }
            }
            Node::If(c, t, f) => {
                if self.guard(c, mode, s0, buf)?.as_bool()? {
                    self.enum_action(t, mode, s0, buf, k)
                } else {
                    self.enum_action(f, mode, s0, buf, k)
                }
            }
            Node::Case(arms, other) => {
                for (c, v) in arms {
                    if self.guard(c, mode, s0, buf)?.as_bool()? {
                        return self.enum_action(v, mode, s0, buf, k);
                    }
                }
                match other {
                    Some(o) => self.enum_action(o, mode, s0, buf, k),
                    None => fail("Attempted to evaluate a CASE expression, but none of the arms' conditions was true."),
                }
            }
            Node::Exists(bounds, body) => {
                let evals = |e: &Ex| self.eval_expr(e, mode, s0, buf);
                let saved = if self.splitting.get() { self.cur_label.borrow().clone() } else { None };
                let split = self.splitting.get();
                self.for_each_binding_cb(bounds, 0, &evals, &mut |_ev| {
                    if split {
                        *self.cur_label.borrow_mut() = saved.clone();
                    }
                    self.enum_action(body, mode, s0, buf, k)?;
                    Ok(true)
                })?;
                if split {
                    *self.cur_label.borrow_mut() = saved;
                }
                Ok(())
            }
            Node::InlineCall { assigns, body } => {
                for (slot, a) in assigns {
                    let s = {
                        let b = buf.borrow();
                        let (z0, z1): (&[Value], &[Value]) = match mode {
                            Mode::Init => (&b, &self.empty()),
                            Mode::Next => (s0, &b),
                        };
                        self.eval_arg_pub(a, z0, z1)?
                    };
                    self.set_slot(*slot, s);
                }
                self.enum_action(body, mode, s0, buf, k)
            }
            Node::Call(d, args, _)
                if d.native.get().is_none()
                    && d.body.borrow().is_some()
                    && (d.level >= tla_sany::sem::Level::State || !self.action_simple(ex, mode, 0)) =>
            {
                self.enum_def_call(d, args, mode, s0, buf, k)
            }
            // Java: user-defined operator passed as a parameter / substituted constant operator: expand its definition
            Node::CallLocal(i, args) => match self.get_slot(*i) {
                Slot::Op(c) => self.enum_closure(&c, args, mode, s0, buf, k),
                _ => self.enum_guard(ex, mode, s0, buf, k),
            },
            Node::CallDecl(dr, args) => {
                let found = {
                    let ss = self.substs.borrow();
                    let mut r = None;
                    for ent in ss.iter() {
                        if ent.decl == dr.id {
                            if let Slot::Op(c) = &ent.slot {
                                r = Some(c.clone());
                            }
                            break;
                        }
                    }
                    r
                };
                match found {
                    Some(c) => self.enum_closure(&c, args, mode, s0, buf, k),
                    None => {
                        let d = self.const_ops.borrow().get(&dr.id).cloned();
                        match d {
                            Some(d) => self.enum_def_call(&d, args, mode, s0, buf, k),
                            None => self.enum_guard(ex, mode, s0, buf, k),
                        }
                    }
                }
            }
            Node::SubstIn(subs, body, cacheable, cache) => {
                let outer = self.substs.borrow().clone();
                if *cacheable {
                    let hit = match &*cache.borrow() {
                        Some((o, res)) if o.same(&outer) => Some(res.clone()),
                        _ => None,
                    };
                    if let Some(res) = hit {
                        *self.substs.borrow_mut() = res;
                        let r = self.enum_action(body, mode, s0, buf, &mut || {
                            // continuation: without the substitutions of this scope
                            let held = std::mem::replace(&mut *self.substs.borrow_mut(), outer.clone());
                            let r = k();
                            *self.substs.borrow_mut() = held;
                            r
                        });
                        *self.substs.borrow_mut() = outer;
                        return r;
                    }
                }
                for (decl, a) in subs {
                    let s = {
                        let b = buf.borrow();
                        let empty = self.empty();
                        let (z0, z1): (&[Value], &[Value]) = match mode {
                            Mode::Init => (&b, &empty),
                            Mode::Next => (s0, &b),
                        };
                        match self.eval_arg_pub(a, z0, z1) {
                            Ok(sl) => sl,
                            Err(e) => {
                                *self.substs.borrow_mut() = outer;
                                return Err(e);
                            }
                        }
                    };
                    let next = self.substs.borrow().push(SubstEntry { decl: *decl, slot: s });
                    *self.substs.borrow_mut() = next;
                }
                if *cacheable {
                    *cache.borrow_mut() = Some((outer.clone(), self.substs.borrow().clone()));
                }
                let r = self.enum_action(body, mode, s0, buf, &mut || {
                    // continuation: without the substitutions of this scope
                    let held = std::mem::replace(&mut *self.substs.borrow_mut(), outer.clone());
                    let r = k();
                    *self.substs.borrow_mut() = held;
                    r
                });
                *self.substs.borrow_mut() = outer;
                r
            }
            Node::LetScope(slots, body) => {
                for s in slots {
                    self.set_slot(*s, Slot::Unset);
                }
                self.enum_action(body, mode, s0, buf, k)
            }
            Node::LetRec(defs, body) => {
                for (slot, l) in defs {
                    let frame = {
                        let st = self.stack.borrow();
                        Rc::new(st[self.base.get()..].to_vec())
                    };
                    let clo = Rc::new(OpClosure::Lambda { def: l.clone(), frame, self_slot: Some(*slot) });
                    self.set_slot(*slot, Slot::Op(clo));
                }
                self.enum_action(body, mode, s0, buf, k)
            }
            // Java: a LazyValue (call-by-name argument such as an action passed to an operator) is expanded
            Node::Local(s) => match self.get_slot(*s) {
                Slot::Lazy(l) => self.enum_in_frame(&l.frame, &l.substs, &[], &l.code, mode, s0, buf, k),
                _ => self.enum_guard(ex, mode, s0, buf, k),
            },
            // Java: OPCODE_fa: applying a (not yet evaluated) function constructor expands its body
            Node::FcnApply(f, a) => {
                let fv = self.eval_expr(f, mode, s0, buf)?;
                if let Value::FcnLam(l) = &fv {
                    let lir = if l.cache.borrow().is_none() { l.body.as_ref().and_then(|b| b.clone().downcast::<LamIr>().ok()) } else { None };
                    if let Some(lir) = lir {
                        let av = self.eval_expr(a, mode, s0, buf)?;
                        if !l.dom.member(&av)? {
                            return fail(format!(
                                "Attempted to apply function:
{}
to argument {}, which is not in the domain of the function.",
                                fv.to_tla(),
                                av.to_tla()
                            ));
                        }
                        let mut assigns: Vec<(u32, Slot)> = vec![];
                        if lir.binds.len() == 1 {
                            let (slot, nvars, tuple) = lir.binds[0];
                            assigns.extend(bind_assigns(slot, nvars, tuple, &av)?);
                        } else {
                            let t = match &av {
                                Value::Tuple(t) => t.clone(),
                                _ => return fail("Internal error: argument of a multi-variable function is not a tuple"),
                            };
                            for (i, (slot, nvars, tuple)) in lir.binds.iter().enumerate() {
                                assigns.extend(bind_assigns(*slot, *nvars, *tuple, &t[i])?);
                            }
                        }
                        if let Some(ss) = lir.self_slot {
                            if let Some(sv) = &*lir.me.borrow() {
                                assigns.push((ss, Slot::V(sv.clone())));
                            }
                        }
                        let caller_base = self.base.get();
                        let nb = self.stack.borrow().len();
                        {
                            let mut st = self.stack.borrow_mut();
                            st.extend(lir.cap.frame.iter().cloned());
                            for (i, sl) in &assigns {
                                let idx = nb + *i as usize;
                                if idx >= st.len() {
                                    st.resize(idx + 1, Slot::Unset);
                                }
                                st[idx] = sl.clone();
                            }
                        }
                        self.base.set(nb);
                        let caller_substs = std::mem::replace(&mut *self.substs.borrow_mut(), lir.cap.substs.clone());
                        self.depth.set(self.depth.get() + 1);
                        let r = if self.depth.get() > 3000 {
                            fail_code(crate::ec::SYSTEM_STACK_OVERFLOW, "Java StackOverflowError: the evaluation recursed too deeply")
                        } else {
                            self.enum_action(&lir.body, mode, s0, buf, &mut || {
                                // the rest of the caller's formula runs in the caller's frame and substitutions
                                self.base.set(caller_base);
                                let callee_substs = std::mem::replace(&mut *self.substs.borrow_mut(), caller_substs.clone());
                                let r = k();
                                *self.substs.borrow_mut() = callee_substs;
                                self.base.set(nb);
                                r
                            })
                        };
                        self.depth.set(self.depth.get() - 1);
                        *self.substs.borrow_mut() = caller_substs;
                        self.base.set(caller_base);
                        self.stack.borrow_mut().truncate(nb);
                        return r;
                    }
                }
                let av = self.eval_expr(a, mode, s0, buf)?;
                match fv.apply(&av)? {
                    Value::Bool(true) => k(),
                    Value::Bool(false) => Ok(()),
                    other => fail(format!("The expression of an action or initial predicate evaluated to the non-boolean value
{}", other.to_tla())),
                }
            }
            // Java: OPCODE_subseteq: `x' \subseteq S` enumerates the subsets of S
            Node::Bi(B::Subseteq, es) if es.len() == 2 && self.target_var(&es[0], mode).is_some() => {
                let i = self.target_var(&es[0], mode).unwrap();
                let unassigned = matches!(buf.borrow()[i as usize], Value::Undef);
                let rset = self.eval_expr(&es[1], mode, s0, buf)?;
                if !rset.is_set_like() {
                    return fail(format!("Attempted to compute the powerset of the non-set value
{}", rset.to_tla()));
                }
                if unassigned {
                    let subs = Value::Subset(Rc::new(rset)).enumerate()?;
                    for e in subs.iter() {
                        self.assign_and_continue(i, e.clone(), mode, buf, k)?;
                    }
                    Ok(())
                } else {
                    let cur = buf.borrow()[i as usize].clone();
                    let sub = Value::Subset(Rc::new(rset));
                    if sub.member(&cur)? {
                        k()
                    } else {
                        Ok(())
                    }
                }
            }
            // Java: OPCODE_implies: evaluate the antecedent; when true the consequent is enumerated (it may split)
            Node::Implies(a, b) => {
                if self.guard(a, mode, s0, buf)?.as_bool()? {
                    self.enum_action(b, mode, s0, buf, k)
                } else {
                    k()
                }
            }
            // Java: OPCODE_bf: all contexts are collected, then the body is processed once per context in sequence
            Node::Forall(bounds, body) if !self.action_simple(body, mode, 0) => {
                let mut ctxs: Vec<Vec<(u32, Slot)>> = vec![];
                {
                    let evals = |e: &Ex| self.eval_expr(e, mode, s0, buf);
                    self.for_each_binding_cb(bounds, 0, &evals, &mut |ev| {
                        let mut snap = vec![];
                        for b in bounds.iter() {
                            for j in 0..b.nvars.max(1) {
                                snap.push((b.slot + j, ev.get_slot(b.slot + j)));
                            }
                        }
                        ctxs.push(snap);
                        Ok(true)
                    })?;
                }
                if ctxs.is_empty() {
                    return k();
                }
                let end = self.stack.borrow().len();
                self.forall_chain(&ctxs, 0, body, mode, s0, buf, end, k)
            }
            Node::Bi(B::Enabled, _) | Node::Not(_) | Node::Equiv(..) | Node::Forall(..) | Node::Neq(..) | Node::NotIn(..) => {
                if self.guard(ex, mode, s0, buf)?.as_bool()? {
                    k()
                } else {
                    Ok(())
                }
            }
            _ => {
                let v = self.guard(ex, mode, s0, buf)?;
                match v {
                    Value::Bool(true) => k(),
                    Value::Bool(false) => Ok(()),
                    other => fail(format!(
                        "The expression of an action or initial predicate evaluated to the non-boolean value\n{}",
                        other.to_tla()
                    )),
                }
            }
        }
    }

    /// `\A` chain (Java: the remaining instances are pushed on the `ActionItemList`): every instance runs the same `body`
    /// node, hence the same frame slots (operator parameters, `\E` witnesses, ...).  The frame `[base, end)` as `body` left
    /// it when it yielded is restored after the next instance returns, for the remaining alternatives of `body`.
    fn forall_chain(&self, ctxs: &[Vec<(u32, Slot)>], i: usize, body: &Ex, mode: Mode, s0: &[Value], buf: &Buf, end: usize, k: &mut Cont) -> R<()> {
        for (slot, s) in &ctxs[i] {
            self.set_slot(*slot, s.clone());
        }
        if i + 1 == ctxs.len() {
            return self.enum_action(body, mode, s0, buf, k);
        }
        self.enum_action(body, mode, s0, buf, &mut || {
            let base = self.base.get();
            let snap: Vec<Slot> = {
                let st = self.stack.borrow();
                st[base..end.min(st.len())].to_vec()
            };
            let r = self.forall_chain(ctxs, i + 1, body, mode, s0, buf, end, k);
            {
                let mut st = self.stack.borrow_mut();
                for (j, s) in snap.into_iter().enumerate() {
                    st[base + j] = s;
                }
            }
            for (slot, s) in &ctxs[i] {
                self.set_slot(*slot, s.clone());
            }
            r
        })
    }

    /// Can the action enumerator process `ex` with at most one continuation and no assignments?
    /// (then it is equivalent to evaluating `ex` as a boolean, which is cheaper)
    pub fn action_simple(&self, ex: &Ex, mode: Mode, depth: u32) -> bool {
        if depth > 6 {
            return false;
        }
        let key = (Rc::as_ptr(ex) as usize, mode == Mode::Next);
        if let Some(&b) = self.simple_memo.borrow().get(&key) {
            return b;
        }
        // guard against recursive definitions
        self.simple_memo.borrow_mut().insert(key, false);
        let r = match &**ex {
            Node::And(items) => items.iter().all(|e| self.action_simple(e, mode, depth + 1)),
            Node::Or(..) | Node::Exists(..) | Node::Case(..) | Node::Unchanged(..) | Node::ActionSub { .. } | Node::FcnApply(..) | Node::CallLocal(..) | Node::CallDecl(..) | Node::LetRec(..) | Node::Local(_) => false,
            Node::Forall(_, b) => self.action_simple(b, mode, depth + 1),
            Node::Implies(_, b) => self.action_simple(b, mode, depth + 1),
            Node::If(_, t, f) => self.action_simple(t, mode, depth + 1) && self.action_simple(f, mode, depth + 1),
            // parameters may stand for (primed) variables: be conservative
            Node::Eq(l, r) => {
                !matches!(&**l, Node::Local(_) | Node::Prime(_))
                    && !matches!(&**r, Node::Local(_) | Node::Prime(_))
                    && self.target_var(l, mode).is_none()
                    && self.target_var(r, mode).is_none()
            }
            Node::In(l, _) => !matches!(&**l, Node::Local(_) | Node::Prime(_)) && self.target_var(l, mode).is_none(),
            Node::InlineCall { .. } | Node::SubstIn(..) => false,
            Node::Call(d, _, _) => {
                if d.native.get().is_none() {
                    match d.body.borrow().as_ref() {
                        Some(b) => {
                            let b = b.clone();
                            self.action_simple(&b, mode, depth + 1)
                        }
                        None => true,
                    }
                } else {
                    true
                }
            }
            _ => true,
        };
        self.simple_memo.borrow_mut().insert(key, r);
        r
    }

    /// enumerate `body` inside a copy of a captured frame; the continuation `k` runs in the caller's frame
    fn enum_in_frame(
        &self,
        frame: &Rc<Vec<Slot>>,
        substs: &Substs,
        assigns: &[(u32, Slot)],
        body: &Ex,
        mode: Mode,
        s0: &[Value],
        buf: &Buf,
        k: &mut Cont,
    ) -> R<()> {
        let caller_base = self.base.get();
        let nb = self.stack.borrow().len();
        {
            let mut st = self.stack.borrow_mut();
            st.extend(frame.iter().cloned());
            for (i, sl) in assigns {
                let idx = nb + *i as usize;
                if idx >= st.len() {
                    st.resize(idx + 1, Slot::Unset);
                }
                st[idx] = sl.clone();
            }
        }
        self.base.set(nb);
        let caller_substs = std::mem::replace(&mut *self.substs.borrow_mut(), substs.clone());
        self.depth.set(self.depth.get() + 1);
        let r = if self.depth.get() > 3000 {
            fail_code(crate::ec::SYSTEM_STACK_OVERFLOW, "Java StackOverflowError: the evaluation recursed too deeply")
        } else {
            self.enum_action(body, mode, s0, buf, &mut || {
                self.base.set(caller_base);
                let callee_substs = std::mem::replace(&mut *self.substs.borrow_mut(), caller_substs.clone());
                let r = k();
                *self.substs.borrow_mut() = callee_substs;
                self.base.set(nb);
                r
            })
        };
        self.depth.set(self.depth.get() - 1);
        *self.substs.borrow_mut() = caller_substs;
        self.base.set(caller_base);
        self.stack.borrow_mut().truncate(nb);
        r
    }

    fn enum_guard(&self, ex: &Ex, mode: Mode, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        match self.guard(ex, mode, s0, buf)? {
            Value::Bool(true) => k(),
            Value::Bool(false) => Ok(()),
            other => fail(format!("The expression of an action or initial predicate evaluated to the non-boolean value
{}", other.to_tla())),
        }
    }

    fn enum_closure(&self, c: &Rc<OpClosure>, args: &[Arg], mode: Mode, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        match &**c {
            OpClosure::Def(d) if d.native.get().is_none() && d.body.borrow().is_some() => self.enum_def_call(d, args, mode, s0, buf, k),
            OpClosure::Decl(id) => {
                let d = self.const_ops.borrow().get(id).cloned();
                match d {
                    Some(d) if d.native.get().is_none() && d.body.borrow().is_some() => self.enum_def_call(&d, args, mode, s0, buf, k),
                    _ => fail("A constant operator was used but has not been assigned a value."),
                }
            }
            OpClosure::Lambda { def, frame, self_slot } => {
                let mut slots: Vec<Slot> = Vec::with_capacity(args.len());
                for a in args {
                    let s = {
                        let b = buf.borrow();
                        let empty = self.empty();
                        let (z0, z1): (&[Value], &[Value]) = match mode {
                            Mode::Init => (&b, &empty),
                            Mode::Next => (s0, &b),
                        };
                        self.eval_arg_pub(a, z0, z1)?
                    };
                    slots.push(s);
                }
                let caller_base = self.base.get();
                let nb = self.stack.borrow().len();
                {
                    let mut st = self.stack.borrow_mut();
                    st.extend(frame.iter().cloned());
                    for (i, s) in slots.into_iter().enumerate() {
                        let idx = nb + def.nslots + i;
                        if idx >= st.len() {
                            st.resize(idx + 1, Slot::Unset);
                        }
                        st[idx] = s;
                    }
                    if let Some(ss) = self_slot {
                        let idx = nb + *ss as usize;
                        if idx >= st.len() {
                            st.resize(idx + 1, Slot::Unset);
                        }
                        st[idx] = Slot::Op(c.clone());
                    }
                }
                self.base.set(nb);
                let caller_substs = self.substs.borrow().clone();
                let r = self.enum_action(&def.body, mode, s0, buf, &mut || {
                    self.base.set(caller_base);
                    let r = k();
                    self.base.set(nb);
                    r
                });
                *self.substs.borrow_mut() = caller_substs;
                self.base.set(caller_base);
                self.stack.borrow_mut().truncate(nb);
                r
            }
            OpClosure::Builtin(_) | OpClosure::Def(_) => fail("Internal error: cannot expand this operator while enumerating an action"),
        }
    }

    /// Java: getNextStatesApplImpl for a user-defined operator: continue with the operator's body
    fn enum_def_call(&self, d: &Rc<CompiledDef>, args: &[Arg], mode: Mode, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        // the arguments are evaluated in the caller's frame and pushed directly into the callee's frame
        let nb = self.stack.borrow().len();
        for a in args {
            let s = {
                let b = buf.borrow();
                let empty = self.empty();
                let (z0, z1): (&[Value], &[Value]) = match mode {
                    Mode::Init => (&b, &empty),
                    Mode::Next => (s0, &b),
                };
                self.eval_arg_pub(a, z0, z1)
            };
            match s {
                Ok(s) => self.stack.borrow_mut().push(s),
                Err(e) => {
                    self.stack.borrow_mut().truncate(nb);
                    return Err(e);
                }
            }
        }
        let body = d.body.borrow().as_ref().unwrap().clone();
        let saved_label = if self.splitting.get() && mode == Mode::Next {
            let base = if args.is_empty() {
                d.label_base.get_or_init(|| Rc::new(LabelBase { name: d.name.clone(), params: vec![], pnames: vec![] })).clone()
            } else {
                let (params, pnames): (Vec<Value>, Vec<tla_sany::sem::Name>) = {
                    let st = self.stack.borrow();
                    let formals = d.src.params.borrow();
                    st[nb..]
                        .iter()
                        .enumerate()
                        .filter_map(|(i, s)| if let Slot::V(v) = s { Some((v.clone(), formals.get(i).map(|p| p.name.clone()).unwrap_or_else(|| std::sync::Arc::from("")))) } else { None })
                        .unzip()
                };
                Rc::new(LabelBase { name: d.name.clone(), params, pnames })
            };
            let stop = Rc::as_ptr(&body) as usize;
            Some(self.cur_label.replace(Some(LabelSpec { base, stop })))
        } else {
            None
        };
        let caller_base = self.base.get();
        let nslots = d.nslots.get().max(args.len());
        let old_len = nb;
        crate::eval::grow_unset(&mut self.stack.borrow_mut(), nb + nslots);
        self.base.set(nb);
        self.depth.set(self.depth.get() + 1);
        let callee_base = nb;
        let r = if self.depth.get() > 3000 {
            fail_code(crate::ec::SYSTEM_STACK_OVERFLOW, "Java StackOverflowError: the evaluation recursed too deeply")
        } else {
            // A body `/\ test /\ rest` whose first conjunct is a plain state-level test of plain-value arguments is decided
            // right here (the action machinery would evaluate that test the same way): most calls of a disjunction of
            // guarded actions fail on it.
            let mut start = 0usize;
            let mut rejected = false;
            let mut failure: Option<Box<TlcErr>> = None;
            if mode == Mode::Next && !self.splitting.get() && !self.eval_only.get() {
                if let Some(t) = first_test(d) {
                    let by_name = self.stack.borrow()[nb..nb + args.len()].iter().any(|s| matches!(s, Slot::Lazy(_)));
                    if !by_name {
                        let res = {
                            let b = buf.borrow();
                            self.eval(&t, s0, &b)
                        };
                        match res {
                            Ok(Value::Bool(true)) => start = 1,
                            Ok(Value::Bool(false)) => rejected = true,
                            Ok(_) => {}
                            Err(e) => failure = Some(e),
                        }
                    }
                }
            }
            if let Some(e) = failure {
                Err(e)
            } else if rejected {
                Ok(())
            } else if start == 1 {
                match &*body {
                    Node::And(items) => {
                        let was = self.splitting.replace(false);
                        let r = self.enum_conj(items, 1, mode, s0, buf, &mut || {
                            self.base.set(caller_base);
                            let r = k();
                            self.base.set(callee_base);
                            r
                        });
                        self.splitting.set(was);
                        r
                    }
                    _ => unreachable!("first_test is only set for conjunctions"),
                }
            } else {
                self.enum_action(&body, mode, s0, buf, &mut || {
                    // the rest of the caller's formula runs in the caller's frame
                    self.base.set(caller_base);
                    let r = k();
                    self.base.set(callee_base);
                    r
                })
            }
        };
        self.depth.set(self.depth.get() - 1);
        self.base.set(caller_base);
        self.stack.borrow_mut().truncate(old_len);
        if let Some(l) = saved_label {
            *self.cur_label.borrow_mut() = l;
        }
        r
    }

    fn enum_conj(&self, items: &[Ex], idx: usize, mode: Mode, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        if idx == items.len() {
            return k();
        }
        if idx + 1 == items.len() {
            return self.enum_action(&items[idx], mode, s0, buf, k);
        }
        self.enum_action(&items[idx], mode, s0, buf, &mut || self.enum_conj(items, idx + 1, mode, s0, buf, k))
    }

    /// variables mentioned by an UNCHANGED argument (variable, tuple of variables, definition of such,
    /// a variable declaration substituted by one of those)
    fn unchanged_vars(&self, ex: &Ex, out: &mut Vec<u32>) -> bool {
        let ss = self.substs.borrow().clone();
        self.unchanged_vars_in(ex, &ss, out)
    }

    fn unchanged_vars_in(&self, ex: &Ex, substs: &Substs, out: &mut Vec<u32>) -> bool {
        match &**ex {
            Node::Var(i) => {
                out.push(*i);
                true
            }
            Node::Decl(dr) if dr.is_var => {
                for ent in substs.iter() {
                    if ent.decl == dr.id {
                        return match &ent.slot {
                            Slot::Lazy(l) => self.unchanged_vars_in(&l.code, &l.substs, out),
                            _ => false,
                        };
                    }
                }
                if dr.var_index != u32::MAX {
                    out.push(dr.var_index);
                    true
                } else {
                    false
                }
            }
            Node::Local(s) => match self.get_slot(*s) {
                Slot::Lazy(l) => self.unchanged_vars_in(&l.code, &l.substs, out),
                _ => false,
            },
            Node::Tuple(es) => es.iter().all(|e| self.unchanged_vars_in(e, substs, out)),
            Node::Call(d, args, _) if args.is_empty() && d.native.get().is_none() => {
                let body = d.body.borrow().clone();
                match body {
                    Some(b) => self.unchanged_vars_in(&b, substs, out),
                    None => false,
                }
            }
            _ => false,
        }
    }

    /// the components of an UNCHANGED argument: tuples (also behind nullary definitions) are split up
    fn unchanged_elems_of(&self, ex: &Ex, out: &mut Vec<Ex>, depth: u32) -> bool {
        if depth > 20 {
            return false;
        }
        match &**ex {
            Node::Tuple(es) => es.iter().all(|e| self.unchanged_elems_of(e, out, depth + 1)),
            Node::Call(d, args, _) if args.is_empty() && d.native.get().is_none() => match d.body.borrow().clone() {
                Some(b) => self.unchanged_elems_of(&b, out, depth + 1),
                None => false,
            },
            _ => {
                out.push(ex.clone());
                true
            }
        }
    }

    /// UNCHANGED inside ENABLED: variables keep their value; a substituted declaration is bound to its current value
    fn unchanged_elems(&self, es: &[Ex], idx: usize, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        if idx == es.len() {
            return k();
        }
        let e = &es[idx];
        let mut vars = vec![];
        if self.unchanged_vars(e, &mut vars) {
            return self.assign_unchanged(&vars, 0, s0, buf, &mut || self.unchanged_elems(es, idx + 1, s0, buf, k));
        }
        if let Node::Decl(dr) = &**e {
            if self.substs.borrow().find(dr.id).is_some() {
                let empty = self.empty();
                let v = self.eval(e, s0, &empty)?;
                let existing = self.virt.borrow().iter().find(|(id, _)| *id == dr.id).map(|(_, x)| x.clone());
                return match existing {
                    Some(old) => {
                        if old.eq_val(&v)? {
                            self.unchanged_elems(es, idx + 1, s0, buf, k)
                        } else {
                            Ok(())
                        }
                    }
                    None => {
                        self.virt.borrow_mut().push((dr.id, v));
                        let res = self.unchanged_elems(es, idx + 1, s0, buf, k);
                        self.virt.borrow_mut().pop();
                        res
                    }
                };
            }
        }
        let same = {
            let b = buf.borrow();
            let before = self.eval(e, s0, &b)?;
            let empty = self.empty();
            let after = self.eval(e, &b, &empty)?;
            before.eq_val(&after)?
        };
        if same {
            self.unchanged_elems(es, idx + 1, s0, buf, k)
        } else {
            Ok(())
        }
    }

    fn unchanged_tuple(&self, es: &[Ex], idx: usize, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        if idx == es.len() {
            return k();
        }
        let mut vars = vec![];
        if self.unchanged_vars(&es[idx], &mut vars) {
            return self.assign_unchanged(&vars, 0, s0, buf, &mut || self.unchanged_tuple(es, idx + 1, s0, buf, k));
        }
        let same = {
            let b = buf.borrow();
            let before = self.eval(&es[idx], s0, &b)?;
            let empty = self.empty();
            let after = self.eval(&es[idx], &b, &empty)?;
            before.eq_val(&after)?
        };
        if same {
            self.unchanged_tuple(es, idx + 1, s0, buf, k)
        } else {
            Ok(())
        }
    }

    fn assign_unchanged(&self, vars: &[u32], idx: usize, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        if idx == vars.len() {
            return k();
        }
        let i = vars[idx];
        let v = s0[i as usize].clone();
        self.assign_and_continue(i, v, Mode::Next, buf, &mut || self.assign_unchanged(vars, idx + 1, s0, buf, k))
    }

    pub fn empty(&self) -> Rc<Vec<Value>> {
        let e = self.empty_cache.borrow().clone();
        if e.len() == self.nvars.get() {
            return e;
        }
        let n = Rc::new(vec![Value::Undef; self.nvars.get()]);
        *self.empty_cache.borrow_mut() = n.clone();
        n
    }
}

impl Ev {
    /// `ENABLED <<A>>_v` when `sub` is given (the successor must change `v`), else `ENABLED A`
    /// Java: `Tool.enabled(pred, c, s0, s1, subscript, IActionItemList.CHANGED)`
    pub fn enabled_changed(&self, ex: &Ex, sub: Option<&Ex>, s0: &[Value]) -> R<bool> {
        let sub = match sub {
            None => return self.enabled(ex, s0),
            Some(x) => x,
        };
        let buf: Buf = RefCell::new(vec![Value::Undef; self.nvars.get()]);
        let was = self.splitting.replace(false);
        let saved_label = self.cur_label.borrow().clone();
        let saved_virt = (self.enabled_depth.get(), self.virt_ptr.get(), std::mem::take(&mut *self.virt.borrow_mut()));
        self.enabled_depth.set(saved_virt.0 + 1);
        self.virt_ptr.set(buf.borrow().as_ptr() as usize);
        let r = self.enum_action(ex, Mode::Next, s0, &buf, &mut || {
            // the successor is complete: does the subscript change?
            let empty = self.empty();
            let cur = self.eval(sub, s0, &empty)?;
            let nxt = {
                let b = buf.borrow();
                self.eval(sub, &b, &empty)?
            };
            if cur.eq_val(&nxt)? {
                Ok(())
            } else {
                Err(Box::new(TlcErr { code: -777, msg: "enabled".into(), not_ported: false, trail: vec![], fp_exc: false, frames: vec![], pass: false }))
            }
        });
        *self.cur_label.borrow_mut() = saved_label;
        self.splitting.set(was);
        self.enabled_depth.set(saved_virt.0);
        self.virt_ptr.set(saved_virt.1);
        *self.virt.borrow_mut() = saved_virt.2;
        match r {
            Ok(()) => Ok(false),
            Err(e) if e.code == -777 => Ok(true),
            // Java binds an INSTANCE-substituted variable `v <- expr` by name when it meets `v' = e`; a successor that does
            // not (yet) determine the variables of `expr` therefore does not fail: the step is possible
            Err(e) if e.msg.contains("is not assigned a value") || e.msg.contains("which is not yet assigned a value") => {
                if std::env::var_os("TLCRS_LIVE_DEBUG").is_some() {
                    eprintln!("ENABLED: treating as enabled after: {}", e.msg);
                }
                Ok(true)
            }
            Err(e) => Err(e),
        }
    }

    /// `ENABLED A` in the state `s0`: does the action have a successor?
    pub fn enabled(&self, ex: &Ex, s0: &[Value]) -> R<bool> {
        let buf: Buf = RefCell::new(vec![Value::Undef; self.nvars.get()]);
        // the successor under construction is a new one: an enclosing enumeration that has assigned all variables does not apply
        let was_eval_only = self.eval_only.replace(false);
        let was = self.splitting.replace(false);
        let saved_label = self.cur_label.borrow().clone();
        let saved_virt = (self.enabled_depth.get(), self.virt_ptr.get(), std::mem::take(&mut *self.virt.borrow_mut()));
        self.enabled_depth.set(saved_virt.0 + 1);
        self.virt_ptr.set(buf.borrow().as_ptr() as usize);
        let r = self.enum_action(ex, Mode::Next, s0, &buf, &mut || {
            Err(Box::new(TlcErr { code: -777, msg: "enabled".into(), not_ported: false, trail: vec![], fp_exc: false, frames: vec![], pass: false }))
        });
        *self.cur_label.borrow_mut() = saved_label;
        self.splitting.set(was);
        self.eval_only.set(was_eval_only);
        self.enabled_depth.set(saved_virt.0);
        self.virt_ptr.set(saved_virt.1);
        *self.virt.borrow_mut() = saved_virt.2;
        match r {
            Ok(()) => Ok(false),
            Err(e) if e.code == -777 => Ok(true),
            Err(e) => Err(e),
        }
    }
}
