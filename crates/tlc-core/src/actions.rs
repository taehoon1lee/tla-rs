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
            (Node::PrimedVar(i), Mode::Next) => Some(*i),
            (Node::Var(i), Mode::Init) => Some(*i),
            (Node::Decl(dr), Mode::Init) if dr.is_var => self.decl_target(dr.id, dr.is_var, dr.var_index, &self.substs.borrow()),
            (Node::Prime(inner), Mode::Next) => match &**inner {
                Node::Decl(dr) if dr.is_var => self.decl_target(dr.id, dr.is_var, dr.var_index, &self.substs.borrow()),
                _ => None,
            },
            _ => None,
        }
    }

    /// the state variable a (possibly substituted) variable declaration stands for
    fn decl_target(&self, id: usize, is_var: bool, var_index: u32, substs: &[SubstEntry]) -> Option<u32> {
        for ent in substs.iter().rev() {
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

    fn code_target(&self, code: &Ex, substs: &[SubstEntry]) -> Option<u32> {
        match &**code {
            Node::Var(i) => Some(*i),
            Node::Decl(dr) => self.decl_target(dr.id, dr.is_var, dr.var_index, substs),
            _ => None,
        }
    }

    /// assign variable `i := v` (or check equality if already assigned) and continue
    fn assign_and_continue(&self, i: u32, v: Value, buf: &Buf, k: &mut Cont) -> R<()> {
        let cur = buf.borrow()[i as usize].clone();
        match cur {
            Value::Undef => {
                buf.borrow_mut()[i as usize] = v.normalize()?;
                let r = k();
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
        match &**ex {
            Node::And(items) => {
                let was = self.splitting.replace(false);
                let r = self.enum_conj(items, 0, mode, s0, buf, k);
                self.splitting.set(was);
                r
            }
            Node::Or(items) => {
                for it in items {
                    let saved = buf.borrow().clone();
                    let r = self.enum_action(it, mode, s0, buf, k);
                    *buf.borrow_mut() = saved;
                    r?;
                }
                Ok(())
            }
            Node::Eq(l, r) => {
                if let Some(i) = self.target_var(l, mode) {
                    let v = self.eval_expr(r, mode, s0, buf)?;
                    return self.assign_and_continue(i, v, buf, k);
                }
                if let Some(i) = self.target_var(r, mode) {
                    // `e = x'`: TLC evaluates the equality; assign when the variable is still unassigned
                    let unassigned = matches!(buf.borrow()[i as usize], Value::Undef);
                    if unassigned {
                        let v = self.eval_expr(l, mode, s0, buf)?;
                        return self.assign_and_continue(i, v, buf, k);
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
                                self.assign_and_continue(i, Value::Int(x), buf, k)?;
                                if x == i32::MAX {
                                    break;
                                }
                                x += 1;
                            }
                            return Ok(());
                        }
                        let elems = sv.enumerate()?;
                        for e in elems.iter() {
                            self.assign_and_continue(i, e.clone(), buf, k)?;
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
                    return self.assign_unchanged(&vars, 0, s0, buf, k);
                }
                if self.guard(ex, mode, s0, buf)?.as_bool()? {
                    k()
                } else {
                    Ok(())
                }
            }
            Node::ActionSub { boxed: true, act, sub } if mode == Mode::Next => {
                // [A]_v  ==  A \/ UNCHANGED v
                let saved = buf.borrow().clone();
                let r = self.enum_action(act, mode, s0, buf, k);
                *buf.borrow_mut() = saved;
                r?;
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
                self.for_each_binding_cb(bounds, 0, &evals, &mut |_ev| {
                    let saved = buf.borrow().clone();
                    let r = self.enum_action(body, mode, s0, buf, k);
                    *buf.borrow_mut() = saved;
                    r?;
                    Ok(true)
                })?;
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
            Node::Call(d, args, _) if d.native.get().is_none() && d.body.borrow().is_some() && d.level >= tla_sany::sem::Level::State => {
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
                let body = d.body.borrow().as_ref().unwrap().clone();
                let saved_label = if self.splitting.get() && !d.src.in_let.get() && d.module != "TLC".into() {
                    let l: Rc<str> = Rc::from(format!(
                        "<{} line {}, col {} to line {}, col {} of module {}>",
                        d.name, body_loc(&d.src).bl, body_loc(&d.src).bc, body_loc(&d.src).el, body_loc(&d.src).ec, d.module
                    ));
                    Some(self.cur_label.replace(Some(l)))
                } else {
                    None
                };
                let caller_base = self.base.get();
                let nslots = d.nslots.get().max(slots.len());
                let old_len = self.stack.borrow().len();
                let nb = old_len;
                {
                    let mut st = self.stack.borrow_mut();
                    st.resize(nb + nslots, Slot::Unset);
                    for (i, s) in slots.drain(..).enumerate() {
                        st[nb + i] = s;
                    }
                }
                self.base.set(nb);
                self.depth.set(self.depth.get() + 1);
                let callee_base = nb;
                let r = if self.depth.get() > 3000 {
                    fail_code(crate::ec::SYSTEM_STACK_OVERFLOW, "Java StackOverflowError: the evaluation recursed too deeply")
                } else {
                    self.enum_action(&body, mode, s0, buf, &mut || {
                        // the rest of the caller's formula runs in the caller's frame
                        self.base.set(caller_base);
                        let r = k();
                        self.base.set(callee_base);
                        r
                    })
                };
                self.depth.set(self.depth.get() - 1);
                self.base.set(caller_base);
                self.stack.borrow_mut().truncate(old_len);
                if let Some(l) = saved_label {
                    *self.cur_label.borrow_mut() = l;
                }
                r
            }
            Node::SubstIn(subs, body) => {
                let n0 = self.substs.borrow().len();
                for (decl, a) in subs {
                    let s = {
                        let b = buf.borrow();
                        let empty = self.empty();
                        let (z0, z1): (&[Value], &[Value]) = match mode {
                            Mode::Init => (&b, &empty),
                            Mode::Next => (s0, &b),
                        };
                        self.eval_arg_pub(a, z0, z1)?
                    };
                    self.substs.borrow_mut().push(SubstEntry { decl: *decl, slot: s });
                }
                let n1 = self.substs.borrow().len();
                let r = self.enum_action(body, mode, s0, buf, &mut || {
                    // continuation: without the substitutions of this scope
                    let held: Vec<SubstEntry> = self.substs.borrow_mut().drain(n0..n1).collect();
                    let r = k();
                    self.substs.borrow_mut().truncate(n0);
                    self.substs.borrow_mut().extend(held);
                    r
                });
                self.substs.borrow_mut().truncate(n0);
                r
            }
            Node::Bi(B::Enabled, _) | Node::Not(_) | Node::Implies(..) | Node::Equiv(..) | Node::Forall(..) | Node::Neq(..) | Node::NotIn(..) => {
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

    fn enum_conj(&self, items: &[Ex], idx: usize, mode: Mode, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        if idx == items.len() {
            return k();
        }
        if idx + 1 == items.len() {
            return self.enum_action(&items[idx], mode, s0, buf, k);
        }
        self.enum_action(&items[idx], mode, s0, buf, &mut || self.enum_conj(items, idx + 1, mode, s0, buf, k))
    }

    /// variables mentioned by an UNCHANGED argument (variable, tuple of variables, definition of such)
    fn unchanged_vars(&self, ex: &Ex, out: &mut Vec<u32>) -> bool {
        match &**ex {
            Node::Var(i) => {
                out.push(*i);
                true
            }
            Node::Decl(dr) if dr.is_var => match self.decl_target(dr.id, dr.is_var, dr.var_index, &self.substs.borrow()) {
                Some(i) => {
                    out.push(i);
                    true
                }
                None => false,
            },
            Node::Tuple(es) => es.iter().all(|e| self.unchanged_vars(e, out)),
            Node::Call(d, args, _) if args.is_empty() && d.native.get().is_none() => {
                let body = d.body.borrow().clone();
                match body {
                    Some(b) => self.unchanged_vars(&b, out),
                    None => false,
                }
            }
            _ => false,
        }
    }

    fn assign_unchanged(&self, vars: &[u32], idx: usize, s0: &[Value], buf: &Buf, k: &mut Cont) -> R<()> {
        if idx == vars.len() {
            return k();
        }
        let i = vars[idx];
        let v = s0[i as usize].clone();
        self.assign_and_continue(i, v, buf, &mut || self.assign_unchanged(vars, idx + 1, s0, buf, k))
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
    /// `ENABLED A` in the state `s0`: does the action have a successor?
    pub fn enabled(&self, ex: &Ex, s0: &[Value]) -> R<bool> {
        let buf: Buf = RefCell::new(vec![Value::Undef; self.nvars.get()]);
        let was = self.splitting.replace(false);
        let saved_label = self.cur_label.borrow().clone();
        let r = self.enum_action(ex, Mode::Next, s0, &buf, &mut || {
            Err(Box::new(TlcErr { code: -777, msg: "enabled".into(), not_ported: false, trail: vec![] }))
        });
        *self.cur_label.borrow_mut() = saved_label;
        self.splitting.set(was);
        match r {
            Ok(()) => Ok(false),
            Err(e) if e.code == -777 => Ok(true),
            Err(e) => Err(e),
        }
    }
}
