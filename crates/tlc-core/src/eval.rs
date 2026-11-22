//! Port of the expression evaluator of `tlc2.tool.impl.Tool` (`eval`, `evalAppl`, ...).
//!
//! The evaluator owns a stack of slots (frames of compiled definitions) behind interior mutability so that
//! lazily evaluated values (functions `[x \in S |-> e]`, filtered infinite sets) can capture it.

use crate::ir::*;
use crate::value::*;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::{Rc, Weak};
use tla_sany::intern;
use tla_sany::sem::{self, B};

pub struct Captured {
    pub frame: Rc<Vec<Slot>>,
    pub substs: Rc<Vec<SubstEntry>>,
    pub s0: Rc<Vec<Value>>,
    pub s1: Rc<Vec<Value>>,
}

pub struct Ev {
    me: Weak<Ev>,
    pub stack: RefCell<Vec<Slot>>,
    pub base: Cell<usize>,
    pub substs: RefCell<Vec<SubstEntry>>,
    pub consts: RefCell<HashMap<usize, Value>>,
    pub const_ops: RefCell<HashMap<usize, Rc<CompiledDef>>>,
    pub depth: Cell<u32>,
    /// text printed by Print/PrintT/Assert etc. (flushed by the driver in order)
    pub out: RefCell<Vec<String>>,
    pub nvars: Cell<usize>,
    pub var_names: RefCell<Vec<sem::Name>>,
    pub set_bound: Cell<i64>,
    /// counters exposed through TLCGet
    pub tlc_registers: RefCell<HashMap<i32, Value>>,
    pub stats: RefCell<HashMap<String, Value>>,
    pub empty_cache: RefCell<Rc<Vec<Value>>>,
    /// label of the action being enumerated (`<Name line .. of module M>`)
    pub cur_label: RefCell<Option<Rc<str>>>,
    /// true while the enumerator may still split disjunctions into named actions
    pub splitting: Cell<bool>,
}

const MAX_DEPTH: u32 = 3000;

fn undef_state(n: usize) -> Vec<Value> {
    vec![Value::Undef; n]
}

impl Ev {
    pub fn new(nvars: usize) -> Rc<Ev> {
        Rc::new_cyclic(|me| Ev {
            me: me.clone(),
            stack: RefCell::new(Vec::with_capacity(4096)),
            base: Cell::new(0),
            substs: RefCell::new(vec![]),
            consts: RefCell::new(HashMap::new()),
            const_ops: RefCell::new(HashMap::new()),
            depth: Cell::new(0),
            out: RefCell::new(vec![]),
            nvars: Cell::new(nvars),
            var_names: RefCell::new(vec![]),
            set_bound: Cell::new(1_000_000),
            tlc_registers: RefCell::new(HashMap::new()),
            stats: RefCell::new(HashMap::new()),
            empty_cache: RefCell::new(Rc::new(vec![Value::Undef; nvars])),
            cur_label: RefCell::new(None),
            splitting: Cell::new(false),
        })
    }

    pub fn rc(&self) -> Rc<Ev> {
        self.me.upgrade().expect("evaluator alive")
    }

    pub fn empty_state(&self) -> Vec<Value> {
        undef_state(self.nvars.get())
    }

    // ------------------------------------------------------------------ frames

    fn push_frame(&self, nslots: usize) -> usize {
        let mut st = self.stack.borrow_mut();
        let nb = st.len();
        st.resize(nb + nslots, Slot::Unset);
        nb
    }

    pub fn set_slot(&self, idx: u32, s: Slot) {
        let b = self.base.get();
        self.stack.borrow_mut()[b + idx as usize] = s;
    }

    fn get_slot(&self, idx: u32) -> Slot {
        let b = self.base.get();
        self.stack.borrow()[b + idx as usize].clone()
    }

    /// run `f` in a new frame of `nslots` slots; the frame is popped afterwards
    pub fn with_frame<T>(&self, nslots: usize, f: impl FnOnce(&Ev) -> R<T>) -> R<T> {
        let old = self.base.get();
        let nb = self.push_frame(nslots);
        self.base.set(nb);
        self.depth.set(self.depth.get() + 1);
        let r = if self.depth.get() > MAX_DEPTH {
            fail_code(crate::ec::SYSTEM_STACK_OVERFLOW, "Java StackOverflowError: the evaluation recursed too deeply")
        } else {
            f(self)
        };
        self.depth.set(self.depth.get() - 1);
        self.stack.borrow_mut().truncate(nb);
        self.base.set(old);
        r
    }

    pub fn capture(&self, s0: &[Value], s1: &[Value]) -> Captured {
        let st = self.stack.borrow();
        let b = self.base.get();
        let frame = Rc::new(st[b..].to_vec());
        let substs = Rc::new(self.substs.borrow().clone());
        Captured { frame, substs, s0: Rc::new(s0.to_vec()), s1: Rc::new(s1.to_vec()) }
    }

    /// evaluate `code` inside a copy of a captured frame, after assigning `assigns`
    pub fn run_captured(&self, cap: &Captured, assigns: &[(u32, Slot)], code: &Ex) -> R<Value> {
        let (s0, s1) = (cap.s0.clone(), cap.s1.clone());
        self.run_captured_in(cap, assigns, code, &s0, &s1)
    }

    pub fn run_captured_in(&self, cap: &Captured, assigns: &[(u32, Slot)], code: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        let old_base = self.base.get();
        let nb = {
            let mut st = self.stack.borrow_mut();
            let nb = st.len();
            st.extend(cap.frame.iter().cloned());
            nb
        };
        self.base.set(nb);
        let saved_substs = std::mem::replace(&mut *self.substs.borrow_mut(), (*cap.substs).clone());
        for (i, sl) in assigns {
            let mut st = self.stack.borrow_mut();
            let idx = nb + *i as usize;
            if idx >= st.len() {
                st.resize(idx + 1, Slot::Unset);
            }
            st[idx] = sl.clone();
        }
        self.depth.set(self.depth.get() + 1);
        let r = if self.depth.get() > MAX_DEPTH {
            fail_code(crate::ec::SYSTEM_STACK_OVERFLOW, "Java StackOverflowError: the evaluation recursed too deeply")
        } else {
            self.eval(code, s0, s1)
        };
        self.depth.set(self.depth.get() - 1);
        *self.substs.borrow_mut() = saved_substs;
        self.stack.borrow_mut().truncate(nb);
        self.base.set(old_base);
        r
    }

    // ------------------------------------------------------------------ arguments

    pub fn eval_arg_pub(&self, a: &Arg, s0: &[Value], s1: &[Value]) -> R<Slot> {
        self.eval_arg(a, s0, s1)
    }

    fn eval_arg(&self, a: &Arg, s0: &[Value], s1: &[Value]) -> R<Slot> {
        match a {
            Arg::Val(e, by_name) => {
                if *by_name {
                    let cap = self.capture(s0, s1);
                    return Ok(Slot::Lazy(Rc::new(LazyArg { code: e.clone(), frame: cap.frame, substs: cap.substs })));
                }
                match self.eval(e, s0, s1) {
                    Ok(v) => Ok(Slot::V(v)),
                    Err(err) => {
                        if err.not_ported || err.code == crate::ec::SYSTEM_STACK_OVERFLOW {
                            Err(err)
                        } else {
                            Ok(Slot::Poison(err))
                        }
                    }
                }
            }
            Arg::Op(r) => Ok(Slot::Op(self.opclosure(r)?)),
        }
    }

    fn opclosure(&self, r: &OpRef) -> R<Rc<OpClosure>> {
        Ok(match r {
            OpRef::Def(d) => Rc::new(OpClosure::Def(d.clone())),
            OpRef::Builtin(b) => Rc::new(OpClosure::Builtin(*b)),
            OpRef::Decl(id) => Rc::new(OpClosure::Decl(*id)),
            OpRef::Local(i) => match self.get_slot(*i) {
                Slot::Op(c) => c,
                _ => return fail("An operator parameter was used as an operator but is not bound to one."),
            },
            OpRef::Lambda(l) => {
                let st = self.stack.borrow();
                let b = self.base.get();
                let frame = Rc::new(st[b..].to_vec());
                Rc::new(OpClosure::Lambda { def: l.clone(), frame })
            }
        })
    }

    pub fn force_slot(&self, s: Slot, s0: &[Value], s1: &[Value]) -> R<Value> {
        match s {
            Slot::V(v) => Ok(v),
            Slot::Poison(e) => Err(e),
            Slot::Lazy(l) => {
                // call-by-name: evaluated in the *current* state context
                let cap = Captured { frame: l.frame.clone(), substs: l.substs.clone(), s0: Rc::new(vec![]), s1: Rc::new(vec![]) };
                self.run_captured_in(&cap, &[], &l.code, s0, s1)
            }
            Slot::Op(_) => fail("An operator was used where a value was expected."),
            Slot::Unset => fail("Internal error: use of an unassigned local variable."),
        }
    }

    // ------------------------------------------------------------------ calls

    fn call_def(&self, d: &Rc<CompiledDef>, args: &[Arg], s0: &[Value], s1: &[Value]) -> R<Value> {
        let mut slots: Vec<Slot> = Vec::with_capacity(args.len());
        for a in args {
            slots.push(self.eval_arg(a, s0, s1)?);
        }
        self.call_def_slots(d, slots, s0, s1)
    }

    pub fn call_def_slots(&self, d: &Rc<CompiledDef>, mut slots: Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
        if let Some(f) = d.native.get() {
            return f(self, &mut slots, s0, s1);
        }
        let cacheable = d.nparams == 0 && d.level == sem::Level::Const;
        if cacheable {
            if let Some(v) = &*d.cache.borrow() {
                return Ok(v.clone());
            }
        }
        let body = match &*d.body.borrow() {
            Some(b) => b.clone(),
            None => return fail(format!("The definition of {} has no body.", d.name)),
        };
        let r = self.with_frame(d.nslots.get().max(slots.len()), |ev| {
            {
                let b = ev.base.get();
                let mut st = ev.stack.borrow_mut();
                for (i, s) in slots.drain(..).enumerate() {
                    st[b + i] = s;
                }
            }
            ev.eval(&body, s0, s1)
        })?;
        if cacheable {
            *d.cache.borrow_mut() = Some(r.clone());
        }
        Ok(r)
    }

    fn apply_closure(&self, c: &Rc<OpClosure>, args: &[Arg], s0: &[Value], s1: &[Value]) -> R<Value> {
        let mut slots: Vec<Slot> = Vec::with_capacity(args.len());
        for a in args {
            slots.push(self.eval_arg(a, s0, s1)?);
        }
        self.apply_closure_slots(c, slots, s0, s1)
    }

    pub fn apply_closure_slots(&self, c: &Rc<OpClosure>, slots: Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
        match &**c {
            OpClosure::Def(d) => self.call_def_slots(d, slots, s0, s1),
            OpClosure::Builtin(b) => {
                let mut vals = vec![];
                for s in slots {
                    vals.push(self.force_slot(s, s0, s1)?);
                }
                self.apply_builtin(*b, vals)
            }
            OpClosure::Lambda { def, frame } => {
                let cap = Captured { frame: frame.clone(), substs: Rc::new(self.substs.borrow().clone()), s0: Rc::new(s0.to_vec()), s1: Rc::new(s1.to_vec()) };
                // parameters occupy consecutive slots starting at `def.nslots`
                let assigns: Vec<(u32, Slot)> = slots.into_iter().enumerate().map(|(i, s)| ((def.nslots + i) as u32, s)).collect();
                self.run_captured(&cap, &assigns, &def.body)
            }
            OpClosure::Decl(id) => {
                let d = self.const_ops.borrow().get(id).cloned();
                match d {
                    Some(d) => self.call_def_slots(&d, slots, s0, s1),
                    None => fail("A constant operator was used but has not been assigned a value."),
                }
            }
        }
    }

    pub fn apply_builtin(&self, b: B, vals: Vec<Value>) -> R<Value> {
        match b {
            B::Eq => Ok(Value::Bool(vals[0].eq_val(&vals[1])?)),
            B::Neq => Ok(Value::Bool(!vals[0].eq_val(&vals[1])?)),
            B::In => Ok(Value::Bool(vals[1].member(&vals[0])?)),
            B::NotIn => Ok(Value::Bool(!vals[1].member(&vals[0])?)),
            B::And => Ok(Value::Bool(vals[0].as_bool()? && vals[1].as_bool()?)),
            B::Or => Ok(Value::Bool(vals[0].as_bool()? || vals[1].as_bool()?)),
            B::Implies => Ok(Value::Bool(!vals[0].as_bool()? || vals[1].as_bool()?)),
            B::Equiv => Ok(Value::Bool(vals[0].as_bool()? == vals[1].as_bool()?)),
            B::Not => Ok(Value::Bool(!vals[0].as_bool()?)),
            _ => self.set_builtin(b, vals),
        }
    }

    fn set_builtin(&self, b: B, vals: Vec<Value>) -> R<Value> {
        match b {
            B::Subset => {
                if !vals[0].is_set_like() {
                    return fail(format!("Attempted to compute the powerset of the non-set value\n{}", vals[0].to_tla()));
                }
                Ok(Value::Subset(Rc::new(vals[0].clone())))
            }
            B::UnionAll => {
                if !vals[0].is_set_like() {
                    return fail(format!("Attempted to apply UNION to the non-set value\n{}", vals[0].to_tla()));
                }
                Ok(Value::BigUnion(Rc::new(vals[0].clone())))
            }
            B::Domain => vals[0].domain(),
            B::Subseteq => {
                if !vals[0].is_set_like() || !vals[1].is_set_like() {
                    return fail(format!(
                        "Attempted to check if the value:\n{}\nis a subset of the value\n{}",
                        vals[0].to_tla(),
                        vals[1].to_tla()
                    ));
                }
                Ok(Value::Bool(vals[0].subseteq(&vals[1])?))
            }
            B::SetMinus | B::Intersect | B::Union => {
                if !vals[0].is_set_like() || !vals[1].is_set_like() {
                    return fail(format!(
                        "Attempted to apply the operator {} to the values\n{}\nand\n{}",
                        b.name(),
                        vals[0].to_tla(),
                        vals[1].to_tla()
                    ));
                }
                let p = Rc::new((vals[0].clone(), vals[1].clone()));
                // eagerly normalize when both operands are cheap finite sets
                let v = match b {
                    B::SetMinus => Value::SetDiff(p),
                    B::Intersect => Value::SetCap(p),
                    _ => Value::SetCup(p),
                };
                if v.is_finite() && matches!((&vals[0], &vals[1]), (Value::Set(_) | Value::Interval(..), Value::Set(_) | Value::Interval(..))) {
                    return Ok(Value::Set(v.enumerate()?));
                }
                Ok(v)
            }
            B::Times => Ok(Value::SetOfTuples(Rc::new(vals))),
            _ => fail(format!("The built-in operator {} cannot be applied here.", b.name())),
        }
    }

    // ------------------------------------------------------------------ the evaluator

    pub fn eval(&self, e: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        match &**e {
            Node::Const(v) => Ok(v.clone()),
            Node::Local(i) => {
                let s = self.get_slot(*i);
                match s {
                    Slot::V(v) => Ok(v),
                    other => self.force_slot(other, s0, s1),
                }
            }
            Node::Var(i) => match &s0[*i as usize] {
                Value::Undef => fail(format!("The variable {} is not assigned a value in the current state.", self.var_name(*i))),
                v => Ok(v.clone()),
            },
            Node::PrimedVar(i) => match s1.get(*i as usize) {
                Some(Value::Undef) | None => fail(format!(
                    "Attempted to evaluate the primed variable {}', which is not yet assigned a value.",
                    self.var_name(*i)
                )),
                Some(v) => Ok(v.clone()),
            },
            Node::Decl(dr) => {
                {
                    let ss = self.substs.borrow();
                    for ent in ss.iter().rev() {
                        if ent.decl == dr.id {
                            let slot = ent.slot.clone();
                            drop(ss);
                            return self.force_slot(slot, s0, s1);
                        }
                    }
                }
                if dr.is_var {
                    match s0.get(dr.var_index as usize) {
                        Some(Value::Undef) | None => fail(format!("The variable {} is not assigned a value in the current state.", dr.name)),
                        Some(v) => Ok(v.clone()),
                    }
                } else {
                    match self.consts.borrow().get(&dr.id) {
                        Some(v) => Ok(v.clone()),
                        None => fail_code(
                            crate::ec::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM,
                            format!("The constant parameter {} is not assigned a value by the configuration file.", dr.name),
                        ),
                    }
                }
            }
            Node::CallDecl(dr, args) => {
                {
                    let ss = self.substs.borrow();
                    for ent in ss.iter().rev() {
                        if ent.decl == dr.id {
                            if let Slot::Op(c) = ent.slot.clone() {
                                drop(ss);
                                return self.apply_closure(&c, args, s0, s1);
                            }
                            break;
                        }
                    }
                }
                let d = self.const_ops.borrow().get(&dr.id).cloned();
                match d {
                    Some(d) => self.call_def(&d, args, s0, s1),
                    None => fail_code(
                        crate::ec::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM,
                        format!("The constant parameter {} is not assigned a value by the configuration file.", dr.name),
                    ),
                }
            }
            Node::Prime(inner) => {
                let empty = self.empty_state();
                self.eval(inner, s1, &empty)
            }
            Node::Unchanged(inner) => {
                let cur = self.eval(inner, s0, s1)?;
                let empty = self.empty_state();
                let nxt = self.eval(inner, s1, &empty)?;
                Ok(Value::Bool(cur.eq_val(&nxt)?))
            }
            Node::Call(d, args, _loc) => self.call_def(d, args, s0, s1),
            Node::CallLocal(i, args) => match self.get_slot(*i) {
                Slot::Op(c) => self.apply_closure(&c, args, s0, s1),
                _ => fail("An operator parameter was applied but is not bound to an operator."),
            },
            Node::InlineCall { assigns, body } => {
                for (slot, a) in assigns {
                    let s = self.eval_arg(a, s0, s1)?;
                    self.set_slot(*slot, s);
                }
                self.eval(body, s0, s1)
            }
            Node::Bi(b, es) => self.eval_bi(*b, es, s0, s1),
            Node::And(es) => {
                for x in es {
                    if !self.eval(x, s0, s1)?.as_bool()? {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            Node::Or(es) => {
                for x in es {
                    if self.eval(x, s0, s1)?.as_bool()? {
                        return Ok(Value::Bool(true));
                    }
                }
                Ok(Value::Bool(false))
            }
            Node::Not(x) => Ok(Value::Bool(!self.eval(x, s0, s1)?.as_bool()?)),
            Node::Implies(a, b) => {
                if !self.eval(a, s0, s1)?.as_bool()? {
                    return Ok(Value::Bool(true));
                }
                Ok(Value::Bool(self.eval(b, s0, s1)?.as_bool()?))
            }
            Node::Equiv(a, b) => {
                let x = self.eval(a, s0, s1)?.as_bool()?;
                let y = self.eval(b, s0, s1)?.as_bool()?;
                Ok(Value::Bool(x == y))
            }
            Node::Eq(a, b) => {
                let x = self.eval(a, s0, s1)?;
                let y = self.eval(b, s0, s1)?;
                Ok(Value::Bool(x.eq_val(&y)?))
            }
            Node::Neq(a, b) => {
                let x = self.eval(a, s0, s1)?;
                let y = self.eval(b, s0, s1)?;
                Ok(Value::Bool(!x.eq_val(&y)?))
            }
            Node::In(a, b) => {
                let x = self.eval(a, s0, s1)?;
                let y = self.eval(b, s0, s1)?;
                Ok(Value::Bool(y.member(&x)?))
            }
            Node::NotIn(a, b) => {
                let x = self.eval(a, s0, s1)?;
                let y = self.eval(b, s0, s1)?;
                Ok(Value::Bool(!y.member(&x)?))
            }
            Node::Tuple(es) => {
                let mut v = Vec::with_capacity(es.len());
                for x in es {
                    v.push(self.eval(x, s0, s1)?);
                }
                Ok(Value::tuple(v))
            }
            Node::SetEnum(es) => {
                let mut v = Vec::with_capacity(es.len());
                for x in es {
                    v.push(self.eval(x, s0, s1)?);
                }
                Value::set_from(v)
            }
            Node::Times(es) => {
                let mut v = Vec::with_capacity(es.len());
                for x in es {
                    let s = self.eval(x, s0, s1)?;
                    if !s.is_set_like() {
                        return fail(format!("Attempted to compute the Cartesian product of the non-set value\n{}", s.to_tla()));
                    }
                    v.push(s);
                }
                Ok(Value::SetOfTuples(Rc::new(v)))
            }
            Node::FcnApply(f, a) => {
                let fv = self.eval(f, s0, s1)?;
                let av = self.eval(a, s0, s1)?;
                fv.apply(&av)
            }
            Node::Record(r, field) => {
                let rv = self.eval(r, s0, s1)?;
                match &rv {
                    Value::Fcn(f) => {
                        for (d, v) in f.dom.iter().zip(f.vals.iter()) {
                            if let Value::Str(id) = d {
                                if id == field {
                                    return Ok(v.clone());
                                }
                            }
                        }
                        fail(format!("Attempted to access nonexistent field '{}' of record\n{}", intern::name_of(*field), rv.to_tla()))
                    }
                    Value::FcnLam(_) => rv.apply(&Value::Str(*field)),
                    _ => fail(format!("Attempted to access field '{}' of the non-record value\n{}", intern::name_of(*field), rv.to_tla())),
                }
            }
            Node::SubsetOf { bound, pred, .. } => {
                let base = self.eval(&bound.set, s0, s1)?;
                if !base.is_set_like() {
                    return fail(format!("Attempted to construct a set of the form {{x \\in S : P}} where S is not a set:\n{}", base.to_tla()));
                }
                if base.is_finite() {
                    let elems = base.enumerate()?;
                    let mut out = Vec::new();
                    for el in elems.iter() {
                        self.bind_bound(bound, el)?;
                        if self.eval(pred, s0, s1)?.as_bool()? {
                            out.push(el.clone());
                        }
                    }
                    Ok(Value::Set(Rc::new(out)))
                } else {
                    let cap = self.capture(s0, s1);
                    let ev = self.rc();
                    let (slot, nvars, tuple) = (bound.slot, bound.nvars, bound.tuple);
                    let pred = pred.clone();
                    Ok(Value::SetPred(Rc::new(SetPred {
                        base,
                        pred: Box::new(move |v: &Value| {
                            let assigns = bind_assigns(slot, nvars, tuple, v)?;
                            ev.run_captured(&cap, &assigns, &pred)?.as_bool()
                        }),
                        cache: RefCell::new(None),
                    })))
                }
            }
            Node::SetOfAll(body, bounds) => {
                let mut out = Vec::new();
                self.for_each_binding(bounds, 0, s0, s1, &mut |ev| {
                    out.push(ev.eval(body, s0, s1)?);
                    Ok(true)
                })?;
                Value::set_from(out)
            }
            Node::FcnCons(bounds, body, self_slot) => {
                if bounds.len() == 1 {
                    let b = &bounds[0];
                    let dom = self.eval(&b.set, s0, s1)?;
                    if !dom.is_set_like() {
                        return fail(format!("Attempted to construct a function over the non-set value\n{}", dom.to_tla()));
                    }
                    let cap = self.capture(s0, s1);
                    let ev = self.rc();
                    let (slot, nvars, tuple) = (b.slot, b.nvars, b.tuple);
                    let body = body.clone();
                    let me: Rc<RefCell<Option<Value>>> = Rc::new(RefCell::new(None));
                    let me2 = me.clone();
                    let self_slot = *self_slot;
                    let v = Value::FcnLam(Rc::new(FcnLam {
                        dom,
                        apply: Box::new(move |v: &Value| {
                            let mut assigns = bind_assigns(slot, nvars, tuple, v)?;
                            if let Some(ss) = self_slot {
                                if let Some(sv) = &*me2.borrow() {
                                    assigns.push((ss, Slot::V(sv.clone())));
                                }
                            }
                            ev.run_captured(&cap, &assigns, &body)
                        }),
                        cache: RefCell::new(None),
                    }));
                    if self_slot.is_some() {
                        *me.borrow_mut() = Some(v.clone());
                    }
                    Ok(v)
                } else {
                    // [x \in S, y \in T |-> e]: a function on tuples
                    let mut doms = vec![];
                    for b in bounds {
                        let d = self.eval(&b.set, s0, s1)?;
                        if !d.is_set_like() {
                            return fail(format!("Attempted to construct a function over the non-set value\n{}", d.to_tla()));
                        }
                        doms.push(d);
                    }
                    let dom = Value::SetOfTuples(Rc::new(doms));
                    let cap = self.capture(s0, s1);
                    let ev = self.rc();
                    let slots: Vec<(u32, u32, bool)> = bounds.iter().map(|b| (b.slot, b.nvars, b.tuple)).collect();
                    let body = body.clone();
                    let me: Rc<RefCell<Option<Value>>> = Rc::new(RefCell::new(None));
                    let me2 = me.clone();
                    let self_slot = *self_slot;
                    let v = Value::FcnLam(Rc::new(FcnLam {
                        dom,
                        apply: Box::new(move |v: &Value| {
                            let t = match v {
                                Value::Tuple(t) => t.clone(),
                                _ => return fail("Internal error: argument of a multi-variable function is not a tuple"),
                            };
                            let mut assigns = vec![];
                            for (i, (slot, nvars, tuple)) in slots.iter().enumerate() {
                                assigns.extend(bind_assigns(*slot, *nvars, *tuple, &t[i])?);
                            }
                            if let Some(ss) = self_slot {
                                if let Some(sv) = &*me2.borrow() {
                                    assigns.push((ss, Slot::V(sv.clone())));
                                }
                            }
                            ev.run_captured(&cap, &assigns, &body)
                        }),
                        cache: RefCell::new(None),
                    }));
                    if self_slot.is_some() {
                        *me.borrow_mut() = Some(v.clone());
                    }
                    Ok(v)
                }
            }
            Node::SetOfFcns(a, b) => {
                let d = self.eval(a, s0, s1)?;
                let r = self.eval(b, s0, s1)?;
                if !d.is_set_like() || !r.is_set_like() {
                    return fail("Attempted to construct a set of functions [S -> T] where S or T is not a set.");
                }
                Ok(Value::SetOfFcns(Rc::new((d, r))))
            }
            Node::RcdCons(fields) => {
                let mut v = Vec::with_capacity(fields.len());
                for (n, x) in fields {
                    v.push((*n, self.eval(x, s0, s1)?));
                }
                Ok(Value::record(v))
            }
            Node::SetOfRcds(fields) => {
                let mut v = Vec::with_capacity(fields.len());
                for (n, x) in fields {
                    let s = self.eval(x, s0, s1)?;
                    if !s.is_set_like() {
                        return fail(format!("Attempted to construct a set of records with the non-set value\n{}", s.to_tla()));
                    }
                    v.push((*n, s));
                }
                Ok(Value::SetOfRcds(Rc::new(v)))
            }
            Node::Except(f, specs) => {
                let mut cur = self.eval(f, s0, s1)?;
                for sp in specs {
                    let mut idx = Vec::with_capacity(sp.path.len());
                    for p in &sp.path {
                        match p {
                            PathIr::Field(n) => idx.push(Value::Str(*n)),
                            PathIr::Index(x) => idx.push(self.eval(x, s0, s1)?),
                        }
                    }
                    cur = self.except_path(&cur, &idx, 0, sp.at_slot, &sp.val, s0, s1)?;
                }
                Ok(cur)
            }
            Node::ActionSub { boxed, act, sub } => {
                let a = self.eval(act, s0, s1)?.as_bool()?;
                let unchanged = {
                    let cur = self.eval(sub, s0, s1)?;
                    let empty = self.empty_state();
                    let nxt = self.eval(sub, s1, &empty)?;
                    cur.eq_val(&nxt)?
                };
                if *boxed {
                    Ok(Value::Bool(a || unchanged))
                } else {
                    Ok(Value::Bool(a && !unchanged))
                }
            }
            Node::If(c, t, f) => {
                if self.eval(c, s0, s1)?.as_bool()? {
                    self.eval(t, s0, s1)
                } else {
                    self.eval(f, s0, s1)
                }
            }
            Node::Case(arms, other) => {
                for (c, v) in arms {
                    if self.eval(c, s0, s1)?.as_bool()? {
                        return self.eval(v, s0, s1);
                    }
                }
                match other {
                    Some(o) => self.eval(o, s0, s1),
                    None => fail("Attempted to evaluate a CASE expression, but none of the arms' conditions was true."),
                }
            }
            Node::Exists(bounds, body) => {
                let mut result = false;
                self.for_each_binding(bounds, 0, s0, s1, &mut |ev| {
                    if ev.eval(body, s0, s1)?.as_bool()? {
                        result = true;
                        return Ok(false);
                    }
                    Ok(true)
                })?;
                Ok(Value::Bool(result))
            }
            Node::Forall(bounds, body) => {
                let mut result = true;
                self.for_each_binding(bounds, 0, s0, s1, &mut |ev| {
                    if !ev.eval(body, s0, s1)?.as_bool()? {
                        result = false;
                        return Ok(false);
                    }
                    Ok(true)
                })?;
                Ok(Value::Bool(result))
            }
            Node::Choose(bound, body) => {
                let set = self.eval(&bound.set, s0, s1)?;
                if !set.is_set_like() {
                    return fail(format!("Attempted to compute CHOOSE x \\in S : P where S is not a set:\n{}", set.to_tla()));
                }
                let elems = set.enumerate()?;
                for el in elems.iter() {
                    self.bind_bound(bound, el)?;
                    if self.eval(body, s0, s1)?.as_bool()? {
                        return Ok(el.clone());
                    }
                }
                fail(format!(
                    "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P."
                ))
            }
            Node::SubstIn(subs, body) => {
                let n0 = self.substs.borrow().len();
                for (decl, a) in subs {
                    let slot = self.eval_arg(a, s0, s1)?;
                    // a substitution value is evaluated in the scope of the instantiating module: it must not see
                    // the substitutions it is about to establish
                    self.substs.borrow_mut().push(SubstEntry { decl: *decl, slot });
                }
                let r = self.eval(body, s0, s1);
                self.substs.borrow_mut().truncate(n0);
                r
            }
            Node::Temporal(_) => fail("Attempted to evaluate a temporal formula in a context where only state predicates are allowed."),
            Node::Unsupported(what) => not_ported(format!("tlc-rs: unsupported construct: {}", what)),
            Node::Fail(msg) => fail(msg.clone()),
        }
    }

    fn var_name(&self, i: u32) -> String {
        self.var_names.borrow().get(i as usize).map(|n| n.to_string()).unwrap_or_else(|| format!("#{}", i))
    }

    fn eval_bi(&self, b: B, es: &[Ex], s0: &[Value], s1: &[Value]) -> R<Value> {
        if b == B::Enabled {
            return Ok(Value::Bool(self.enabled(&es[0], s0)?));
        }
        let mut vals = Vec::with_capacity(es.len());
        for x in es {
            vals.push(self.eval(x, s0, s1)?);
        }
        match b {
            B::Enabled => unreachable!(),
            B::Cdot => not_ported("\\cdot"),
            _ => self.apply_builtin(b, vals),
        }
    }

    /// assign the bound variables of `b` from the element `el`
    pub fn bind_bound(&self, b: &BoundIr, el: &Value) -> R<()> {
        if b.nvars == 1 && !b.tuple {
            self.set_slot(b.slot, Slot::V(el.clone()));
            return Ok(());
        }
        let assigns = bind_assigns(b.slot, b.nvars, b.tuple, el)?;
        for (i, s) in assigns {
            self.set_slot(i, s);
        }
        Ok(())
    }

    /// iterate over all combinations of the bounds; `f` returns `false` to stop
    pub fn for_each_binding(
        &self,
        bounds: &[BoundIr],
        i: usize,
        s0: &[Value],
        s1: &[Value],
        f: &mut dyn FnMut(&Ev) -> R<bool>,
    ) -> R<bool> {
        let evals = |e: &Ex| self.eval(e, s0, s1);
        self.for_each_binding_cb(bounds, i, &evals, f)
    }

    pub fn for_each_binding_cb(
        &self,
        bounds: &[BoundIr],
        i: usize,
        evals: &dyn Fn(&Ex) -> R<Value>,
        f: &mut dyn FnMut(&Ev) -> R<bool>,
    ) -> R<bool> {
        if i == bounds.len() {
            return f(self);
        }
        let b = &bounds[i];
        let set = evals(&b.set)?;
        if !set.is_set_like() {
            return fail(format!(
                "Attempted to enumerate the elements of the non-set value\n{}\nin a quantifier or set constructor.",
                set.to_tla()
            ));
        }
        if let Value::Interval(lo, hi) = &set {
            let mut k = *lo;
            while k <= *hi {
                self.bind_bound(b, &Value::Int(k))?;
                if !self.for_each_binding_cb(bounds, i + 1, evals, f)? {
                    return Ok(false);
                }
                if k == i32::MAX {
                    break;
                }
                k += 1;
            }
            return Ok(true);
        }
        let elems = set.enumerate()?;
        for el in elems.iter() {
            self.bind_bound(b, el)?;
            if !self.for_each_binding_cb(bounds, i + 1, evals, f)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn except_path(&self, cur: &Value, idx: &[Value], k: usize, at_slot: u32, val: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        let arg = &idx[k];
        let sub = match cur.apply(arg) {
            Ok(v) => Some(v),
            Err(e) => {
                if k + 1 == idx.len() {
                    None
                } else {
                    return Err(e);
                }
            }
        };
        if k + 1 == idx.len() {
            // `@` is the current value at the path
            match &sub {
                Some(old) => self.set_slot(at_slot, Slot::V(old.clone())),
                None => self.set_slot(at_slot, Slot::Poison(Box::new(TlcErr { code: crate::ec::GENERAL, msg: "Attempted to evaluate @ for a function argument outside the domain.".into(), not_ported: false, trail: vec![] }))),
            }
            if sub.is_none() {
                // outside the domain: TLC leaves the function unchanged
                return Ok(cur.clone());
            }
            let nv = self.eval(val, s0, s1)?;
            cur.except1(arg, nv)
        } else {
            let inner = self.except_path(&sub.unwrap(), idx, k + 1, at_slot, val, s0, s1)?;
            cur.except1(arg, inner)
        }
    }
}

/// slots to assign when binding `v` to the variables of a bound (`x`, `x, y`, or `<<x, y>>`)
pub fn bind_assigns(slot: u32, nvars: u32, tuple: bool, v: &Value) -> R<Vec<(u32, Slot)>> {
    if !tuple {
        let mut out = Vec::with_capacity(nvars as usize);
        for i in 0..nvars {
            out.push((slot + i, Slot::V(v.clone())));
        }
        return Ok(out);
    }
    match v {
        Value::Tuple(t) if t.len() == nvars as usize => Ok(t.iter().enumerate().map(|(i, x)| (slot + i as u32, Slot::V(x.clone()))).collect()),
        _ => fail(format!(
            "Attempted to bind the tuple of {} variables to the value\n{}",
            nvars,
            v.to_tla()
        )),
    }
}
