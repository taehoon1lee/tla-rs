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

#[cfg(feature = "prof")]
pub static PROF_ON: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
#[cfg(feature = "prof")]
pub static PROF_CUR: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
/// the definition (`Rc<CompiledDef>` address) whose body is being evaluated (innermost user-defined operator)
#[cfg(feature = "prof")]
pub static PROF_DEF: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

#[cfg(feature = "prof")]
pub fn node_kind(n: &Node) -> String {
    match n {
        Node::Const(_) => "Const".into(),
        Node::Local(_) => "Local".into(),
        Node::Var(_) => "Var".into(),
        Node::PrimedVar(..) => "PrimedVar".into(),
        Node::Decl(d) => format!("Decl({})", d.name),
        Node::CallDecl(..) => "CallDecl".into(),
        Node::Prime(_) => "Prime".into(),
        Node::Unchanged(_) => "Unchanged".into(),
        Node::Call(d, ..) => format!("Call({})", d.name),
        Node::CallLocal(..) => "CallLocal".into(),
        Node::Bi(b, _) => format!("Bi({:?})", b),
        Node::And(_) => "And".into(),
        Node::Or(_) => "Or".into(),
        Node::Not(_) => "Not".into(),
        Node::Implies(..) => "Implies".into(),
        Node::Equiv(..) => "Equiv".into(),
        Node::Eq(..) => "Eq".into(),
        Node::Neq(..) => "Neq".into(),
        Node::In(..) => "In".into(),
        Node::NotIn(..) => "NotIn".into(),
        Node::Tuple(_) => "Tuple".into(),
        Node::SetEnum(_) => "SetEnum".into(),
        Node::FcnApply(..) => "FcnApply".into(),
        Node::Record(..) => "Record".into(),
        Node::SubsetOf { .. } => "SubsetOf".into(),
        Node::SetOfAll(..) => "SetOfAll".into(),
        Node::FcnCons(..) => "FcnCons".into(),
        Node::Memo(m) => format!("Memo({})", node_kind(&m.inner)),
        Node::Except(..) => "Except".into(),
        Node::If(..) => "If".into(),
        Node::Exists(..) => "Exists".into(),
        Node::Forall(..) => "Forall".into(),
        Node::Choose(..) => "Choose".into(),
        Node::SubstIn(..) => "SubstIn".into(),
        Node::RcdCons(..) => "RcdCons".into(),
        _ => "Other".into(),
    }
}

/// hash of the values of the variables `deps` in `s0`; `None` when one of them is unassigned or cannot be hashed
fn dep_key(deps: &[u32], s0: &[Value]) -> Option<u64> {
    let mut h = Hasher::new();
    for &i in deps {
        let v = s0.get(i as usize)?;
        if matches!(v, Value::Undef) {
            return None;
        }
        v.hash_into(&mut h).ok()?;
    }
    Some(h.finish())
}

/// `CompiledDef::memo` for a state-level definition without parameters: its value for the values of the variables it reads
/// (no counterpart in Java). Switched off (`memo_kind` = 2) when fewer than a quarter of the lookups hit.
#[inline(never)]
fn dep_memo_get(d: &CompiledDef, deps: &[u32], s0: &[Value]) -> Option<Value> {
    let key = dep_key(deps, s0)?;
    d.memo_calls.set(d.memo_calls.get() + 1);
    if let Some(bucket) = d.memo.borrow().get(&key) {
        for (a, r) in bucket {
            if a.len() == deps.len() && deps.iter().zip(a.iter()).all(|(&i, v)| s0[i as usize].eq_val(v).unwrap_or(false)) {
                d.memo_hits.set(d.memo_hits.get() + 1);
                return Some(r.clone());
            }
        }
    }
    if d.memo_calls.get() >= 256 && d.memo_hits.get() * 4 < d.memo_calls.get() {
        d.memo_kind.set(2);
        d.memo.borrow_mut().clear();
        d.memo_n.set(0);
    }
    None
}

#[inline(never)]
fn dep_memo_put(d: &CompiledDef, deps: &[u32], s0: &[Value], v: &Value) {
    if let Some(key) = dep_key(deps, s0) {
        if d.memo_n.get() >= 65_536 {
            d.memo.borrow_mut().clear();
            d.memo_n.set(0);
        }
        let vals: Vec<Value> = deps.iter().map(|&i| s0[i as usize].clone()).collect();
        d.memo.borrow_mut().entry(key).or_default().push((vals, v.clone()));
        d.memo_n.set(d.memo_n.get() + 1);
    }
}

#[derive(Clone)]
pub struct Captured {
    pub frame: Rc<Vec<Slot>>,
    pub substs: Substs,
    pub s0: Rc<Vec<Value>>,
    pub s1: Rc<Vec<Value>>,
}

/// Java: `Action.getLocation`: the name, parameter values and source position of the action a state came from
#[derive(Clone)]
pub struct LabelSpec {
    pub base: Rc<LabelBase>,
    /// address of the `Node` the action was split down to (its location is printed)
    pub stop: usize,
}

/// Java: `CallStackTool`: the node is on the stack of an error that leaves it (out of line: errors are rare, the evaluator is hot)
#[cold]
#[inline(never)]
pub fn push_frame(er: &mut TlcErr, node: usize) {
    er.frames.push(node);
}

pub struct LabelBase {
    pub name: sem::Name,
    pub params: Vec<Value>,
    /// names of the parameters that carry a value (same order as `params`)
    pub pnames: Vec<sem::Name>,
}

/// Java: FcnLambdaValue.body / params / context, kept so `getNextStates` can expand a function application
pub struct LamIr {
    pub cap: Captured,
    /// (slot, nvars, tuple) of every bound group
    pub binds: Vec<(u32, u32, bool)>,
    pub body: Ex,
    pub self_slot: Option<u32>,
    pub me: Rc<RefCell<Option<Value>>>,
}

/// The evaluation stack of local slots. A plain `UnsafeCell` instead of a `RefCell`: the borrow flag checks showed up in
/// profiles and every access is short-lived (no reference is kept across a call into the evaluator).
/// multiplicative hash for pointer-sized keys (the default SipHash dominated the label lookups)
#[derive(Default)]
pub struct PtrHasher(u64);

impl std::hash::Hasher for PtrHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = (self.0.rotate_left(8) ^ *b as u64).wrapping_mul(0x9E3779B97F4A7C15);
        }
    }
    fn write_usize(&mut self, i: usize) {
        self.0 = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
    }
}

pub struct Stack(std::cell::UnsafeCell<Vec<Slot>>);

impl Stack {
    pub fn new(v: Vec<Slot>) -> Stack {
        Stack(std::cell::UnsafeCell::new(v))
    }
    #[inline(always)]
    pub fn borrow(&self) -> &Vec<Slot> {
        unsafe { &*self.0.get() }
    }
    #[allow(clippy::mut_from_ref)]
    #[inline(always)]
    pub fn borrow_mut(&self) -> &mut Vec<Slot> {
        unsafe { &mut *self.0.get() }
    }
}

pub struct Ev {
    me: Weak<Ev>,
    pub stack: Stack,
    pub base: Cell<usize>,
    pub substs: RefCell<Substs>,
    pub consts: RefCell<HashMap<usize, Value>>,
    pub const_ops: RefCell<HashMap<usize, Rc<CompiledDef>>>,
    pub depth: Cell<u32>,
    /// text printed by Print/PrintT/Assert etc. (flushed by the driver in order)
    pub out: RefCell<Vec<String>>,
    /// warnings (`MP.printWarning`) raised while evaluating: `(code, text)`, flushed by the driver in order
    pub warnings: RefCell<Vec<(i32, String)>>,
    pub nvars: Cell<usize>,
    pub var_names: RefCell<Vec<sem::Name>>,
    pub set_bound: Cell<i64>,
    /// counters exposed through TLCGet
    pub tlc_registers: RefCell<HashMap<i32, Value>>,
    /// Java: `IdThread.namedRegisters`: `TLCSet("s:...", v)` / `TLCGet("s:...")` (one worker)
    pub named_regs: RefCell<std::collections::BTreeMap<String, Value>>,
    /// Java: `OpRcdValue`: a constant operator given by the configuration file (`CONSTANT F(0) = 1`): declaration id ->
    /// (argument values, value) in the order of the file
    pub const_tables: RefCell<HashMap<usize, Rc<Vec<(Vec<Value>, Value)>>>>,
    /// `-seed`: the generator behind `RandomElement` (Java: `RandomEnumerableValues`), created on first use
    pub seed: Cell<i64>,
    pub rng: RefCell<Option<crate::jrandom::JRandom>>,
    /// Java: the generator of a worker thread (`TLCStateRandom`): it is seeded with the fingerprint of the state whose successors
    /// are computed (`pred_state`), once per state (`pred_id` counts the states)
    pub wrng: RefCell<Option<crate::jrandom::JRandom>>,
    pub pred_state: RefCell<Option<Vec<Value>>>,
    pub pred_id: Cell<u64>,
    pub rng_for: Cell<u64>,
    /// `-fp`: the irreducible polynomial of the fingerprints Java seeds its random choices with
    pub fp_index: Cell<usize>,
    pub stats: RefCell<HashMap<String, Value>>,
    pub empty_cache: RefCell<Rc<Vec<Value>>>,
    /// label of the action being enumerated (`<Name line .. of module M>`)
    pub cur_label: RefCell<Option<LabelSpec>>,
    /// source info for action labels (filled when the specification is compiled)
    pub node_info: RefCell<HashMap<usize, NodeInfo, std::hash::BuildHasherDefault<PtrHasher>>>,
    /// true while the enumerator may still split disjunctions into named actions
    pub splitting: Cell<bool>,
    /// memo for `Ev::action_simple`: (node address, mode) -> may the action enumerator produce at most one continuation
    pub simple_memo: RefCell<HashMap<(usize, bool), bool>>,
    /// `actions.rs` `or_plan`: (disjunction node address) -> its guard-dispatch plan, if it has one
    pub or_plans: RefCell<HashMap<usize, Option<Rc<crate::actions::OrPlan>>, std::hash::BuildHasherDefault<PtrHasher>>>,
    /// Java: Tool.getNextStatesAllAssigned: once every variable is assigned the remaining conjuncts are only evaluated
    pub eval_only: Cell<bool>,
    /// bumped whenever the state data a cached lazy value may depend on changes (see `LazyArg::cache`)
    pub epoch: Cell<u64>,
    /// reusable argument vectors for native operator calls (saves an allocation per call)
    pub slot_pool: RefCell<Vec<Vec<Slot>>>,
    /// TLCGet("level"|"generated"|"distinct"|"queue"|"diameter"|"duration") (maintained by the model checker)
    pub counters: Cell<[i64; 6]>,
    /// start of the model checking run: `TLCGet("duration")` is computed from it when it is read (not on every state)
    pub start_time: Cell<Option<std::time::Instant>>,
    /// Java: the value `TLCExt!CounterExample` is bound to while the POSTCONDITION is evaluated (`Tool.checkPostConditionWithCounterExample`)
    /// Java: `CallStackTool`: while set, every failure records the nodes it passes (`TlcErr::frames`); set only while a failure is replayed
    pub tracking: Cell<bool>,
    /// the next `eval_inner` runs its body untracked (see `eval_tracked`)
    pub track_skip: Cell<bool>,
    pub counter_example: RefCell<Option<Value>>,
    /// Java: `Tool.evalAlias(.., prefix)`: the value of `TLCExt!Trace` while an ALIAS is evaluated
    pub alias_trace: RefCell<Option<Vec<Value>>>,
    /// true while the specification is processed (Java: `TLCGlobals.mainChecker == null`): the model checker's counters
    /// are not available yet
    pub setup_phase: Cell<bool>,
    /// number of enclosing primes: `TLCGet("level")'` is the level of the successor state
    pub prime_depth: Cell<u32>,
    pub no_frame: Rc<Vec<Slot>>,
    pub no_state: Rc<Vec<Value>>,
    /// Java: TLCGlobals.warn (false with -nowarning): disables the all-assigned fast path
    pub warn: Cell<bool>,
    /// > 0 while `ENABLED` is being evaluated
    pub enabled_depth: Cell<u32>,
    /// inside `ENABLED`: `v' = e` where `v` is an INSTANCE-substituted declaration (not a state variable) binds `v` by
    /// name in the successor state (Java: `TLCStateFun.bind`); (declaration id, value)
    pub virt: RefCell<Vec<(usize, Value)>>,
    /// address of the successor-state buffer the virtual bindings belong to
    pub virt_ptr: Cell<usize>,
}

const MAX_DEPTH: u32 = 3000;

/// a frame slot value that may be part of a `Node::Memo` key: evaluated (no lazy set / function / operator)
fn memo_key_value(v: &Value) -> bool {
    matches!(
        v,
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) | Value::Interval(..) | Value::Set(_) | Value::Tuple(_) | Value::Fcn(_)
    )
}

/// extend a frame stack to `len` slots with `Slot::Unset` (a plain tag-store loop; `Vec::resize` clones through `Slot::clone`)
#[inline(always)]
pub fn grow_unset(st: &mut Vec<Slot>, len: usize) {
    if st.len() < len {
        st.reserve(len - st.len());
        while st.len() < len {
            st.push(Slot::Unset);
        }
    }
}

fn undef_state(n: usize) -> Vec<Value> {
    vec![Value::Undef; n]
}


/// Java: `Tool.eval` of `\cup`, `\cap` and `\` when an operand is an unnormalized set enumeration: an enumerated left operand
/// (`Reducible`) builds the result element by element, in stored order, asking the other set for membership, so an element
/// that cannot be compared with the other set's elements fails exactly where Java fails
fn reduce_unnormalized(b: B, l: &Value, r: &Value) -> Option<R<Value>> {
    if !(matches!(l, Value::SetU(_)) || matches!(r, Value::SetU(_))) {
        return None;
    }
    let reducible = |v: &Value| matches!(v, Value::Set(_) | Value::Interval(..) | Value::SetU(_));
    // the other operand of a set enumeration written in the specification is not normalized either: it is searched linearly
    let member = |o: &Value, e: &Value| -> R<bool> {
        match o {
            Value::Set(v) => linear_member(v, e),
            _ => o.member(e),
        }
    };
    let filter = |a: &Value, o: &Value, keep: bool| -> R<Value> {
        let mut out = vec![];
        for e in a.stored_elems()? {
            if member(o, &e)? == keep {
                out.push(e);
            }
        }
        Ok(Value::SetU(Rc::new(out)))
    };
    match b {
        B::SetMinus if reducible(l) => Some(filter(l, r, false)),
        B::Intersect if reducible(l) => Some(filter(l, r, true)),
        B::Intersect if reducible(r) => Some(filter(r, l, true)),
        B::Union => {
            let (a, o) = if reducible(l) { (l, r) } else if reducible(r) { (r, l) } else { return None };
            if a.is_empty_set().unwrap_or(false) {
                return Some(Ok(o.clone()));
            }
            if !reducible(o) {
                return None;
            }
            Some((|| {
                let mut out = a.stored_elems()?;
                for e in o.enumerate()?.iter() {
                    if !a.member(e)? {
                        out.push(e.clone());
                    }
                }
                Ok(Value::SetU(Rc::new(out)))
            })())
        }
        _ => None,
    }
}

/// Java: `UnionValue.union`: `UNION S` of an enumerated set whose elements are all set enumerations is computed at once, element by
/// element in stored order, asking the partial result for membership
fn union_unnormalized(v: &Value) -> Option<R<Value>> {
    let outer: &[Value] = match v {
        Value::SetU(x) => x,
        Value::Set(x) if x.iter().any(|e| matches!(e, Value::SetU(_))) => x,
        _ => return None,
    };
    if !outer.iter().all(|e| matches!(e, Value::Set(_) | Value::SetU(_))) {
        return None;
    }
    Some((|| {
        let mut res: Vec<Value> = vec![];
        for inner in outer {
            for e in inner.stored_elems()? {
                if !linear_member(&res, &e)? {
                    res.push(e);
                }
            }
        }
        Ok(Value::SetU(Rc::new(res)))
    })())
}

impl Ev {
    pub fn new(nvars: usize) -> Rc<Ev> {
        Rc::new_cyclic(|me| Ev {
            me: me.clone(),
            stack: Stack::new(Vec::with_capacity(4096)),
            base: Cell::new(0),
            substs: RefCell::new(Substs::default()),
            consts: RefCell::new(HashMap::new()),
            const_ops: RefCell::new(HashMap::new()),
            depth: Cell::new(0),
            out: RefCell::new(vec![]),
            warnings: RefCell::new(vec![]),
            nvars: Cell::new(nvars),
            var_names: RefCell::new(vec![]),
            set_bound: Cell::new(1_000_000),
            tlc_registers: RefCell::new(HashMap::new()),
            named_regs: RefCell::new(std::collections::BTreeMap::new()),
            const_tables: RefCell::new(HashMap::new()),
            seed: Cell::new(0),
            rng: RefCell::new(None),
            stats: RefCell::new(HashMap::new()),
            empty_cache: RefCell::new(Rc::new(vec![Value::Undef; nvars])),
            cur_label: RefCell::new(None),
            node_info: RefCell::new(HashMap::default()),
            splitting: Cell::new(false),
            simple_memo: RefCell::new(HashMap::new()),
            or_plans: RefCell::new(HashMap::default()),
            eval_only: Cell::new(false),
            epoch: Cell::new(1),
            slot_pool: RefCell::new(Vec::new()),
            counters: Cell::new([0; 6]),
            start_time: Cell::new(None),
            tracking: Cell::new(false),
            track_skip: Cell::new(false),
            counter_example: RefCell::new(None),
            wrng: RefCell::new(None),
            pred_state: RefCell::new(None),
            pred_id: Cell::new(0),
            rng_for: Cell::new(0),
            fp_index: Cell::new(0),
            alias_trace: RefCell::new(None),
            setup_phase: Cell::new(false),
            prime_depth: Cell::new(0),
            no_frame: Rc::new(Vec::new()),
            no_state: Rc::new(Vec::new()),
            warn: Cell::new(true),
            enabled_depth: Cell::new(0),
            virt: RefCell::new(Vec::new()),
            virt_ptr: Cell::new(0),
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
        grow_unset(&mut st, nb + nslots);
        nb
    }

    pub fn set_slot(&self, idx: u32, s: Slot) {
        let b = self.base.get();
        self.stack.borrow_mut()[b + idx as usize] = s;
    }

    pub fn get_slot(&self, idx: u32) -> Slot {
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
        let substs = self.substs.borrow().clone();
        Captured { frame, substs, s0: Rc::new(s0.to_vec()), s1: Rc::new(s1.to_vec()) }
    }

    /// evaluate `code` inside a copy of a captured frame, after assigning `assigns`
    pub fn run_captured(&self, cap: &Captured, assigns: &[(u32, Slot)], code: &Ex) -> R<Value> {
        let (s0, s1) = (cap.s0.clone(), cap.s1.clone());
        self.run_captured_in(cap, assigns, code, &s0, &s1)
    }

    pub fn run_captured_in(&self, cap: &Captured, assigns: &[(u32, Slot)], code: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        self.run_frame_in(&cap.frame, &cap.substs, assigns, code, s0, s1)
    }

    /// apply a LAMBDA closure in the current state: `run_frame_in` with the captured frame and the current substitutions (which
    /// `apply_closure_slots` passes unchanged), the arguments moved into the parameter slots (`def.nslots + i`), then the closure
    /// itself into `self_slot`
    #[allow(clippy::too_many_arguments)]
    #[inline(never)]
    fn run_lambda(&self, c: &Rc<OpClosure>, def: &LambdaDef, frame: &[Slot], self_slot: Option<u32>, params: &mut [Slot], s0: &[Value], s1: &[Value]) -> R<Value> {
        let old_base = self.base.get();
        let nb = {
            let st = self.stack.borrow_mut();
            let nb = st.len();
            st.extend(frame.iter().cloned());
            for (i, p) in params.iter_mut().enumerate() {
                let idx = nb + def.nslots + i;
                if idx >= st.len() {
                    st.resize(idx + 1, Slot::Unset);
                }
                st[idx] = std::mem::replace(p, Slot::Unset);
            }
            if let Some(ss) = self_slot {
                let idx = nb + ss as usize;
                if idx >= st.len() {
                    st.resize(idx + 1, Slot::Unset);
                }
                st[idx] = Slot::Op(c.clone());
            }
            nb
        };
        self.base.set(nb);
        self.depth.set(self.depth.get() + 1);
        let r = if self.depth.get() > MAX_DEPTH {
            fail_code(crate::ec::SYSTEM_STACK_OVERFLOW, "Java StackOverflowError: the evaluation recursed too deeply")
        } else {
            self.eval(&def.body, s0, s1)
        };
        self.depth.set(self.depth.get() - 1);
        self.stack.borrow_mut().truncate(nb);
        self.base.set(old_base);
        r
    }

    /// evaluate `code` in a copy of `frame` under the substitutions `substs`, in the states `s0`, `s1`
    pub fn run_frame_in(&self, frame: &[Slot], substs: &Substs, assigns: &[(u32, Slot)], code: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        let old_base = self.base.get();
        let nb = {
            let mut st = self.stack.borrow_mut();
            let nb = st.len();
            st.extend(frame.iter().cloned());
            nb
        };
        self.base.set(nb);
        let saved_substs = std::mem::replace(&mut *self.substs.borrow_mut(), substs.clone());
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
            Arg::State(e, closed) => {
                let frame = if *closed {
                    self.no_frame.clone()
                } else {
                    let st = self.stack.borrow();
                    Rc::new(st[self.base.get()..].to_vec())
                };
                let substs = self.substs.borrow().clone();
                Ok(Slot::Lazy(Rc::new(LazyArg { code: e.clone(), frame, substs, cacheable: true, cache: RefCell::new(Vec::new()) })))
            }
            Arg::ValClosed(e) => {
                let substs = self.substs.borrow().clone();
                Ok(Slot::Lazy(Rc::new(LazyArg { code: e.clone(), frame: self.no_frame.clone(), substs, cacheable: false, cache: RefCell::new(Vec::new()) })))
            }
            Arg::Val(e, by_name) => {
                if *by_name {
                    if matches!(&**e, Node::Var(_) | Node::PrimedVar(..)) {
                        // a plain state variable does not depend on the frame or on substitutions
                        return Ok(Slot::Lazy(Rc::new(LazyArg { code: e.clone(), frame: self.no_frame.clone(), substs: Substs::default(), cacheable: false, cache: RefCell::new(Vec::new()) })));
                    }
                    let frame = {
                        let st = self.stack.borrow();
                        Rc::new(st[self.base.get()..].to_vec())
                    };
                    let substs = self.substs.borrow().clone();
                    return Ok(Slot::Lazy(Rc::new(LazyArg { code: e.clone(), frame, substs, cacheable: false, cache: RefCell::new(Vec::new()) })));
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
            OpRef::Decl(id) => {
                // a declared operator that an enclosing INSTANCE substitutes stands for the substituted operator
                let sub = {
                    let ss = self.substs.borrow();
                    ss.find(*id).map(|e| e.slot.clone())
                };
                match sub {
                    Some(Slot::Op(c)) => c,
                    _ => Rc::new(OpClosure::Decl(*id)),
                }
            }
            OpRef::Local(i) => match self.get_slot(*i) {
                Slot::Op(c) => c,
                _ => return fail("An operator parameter was used as an operator but is not bound to one."),
            },
            OpRef::Lambda(l) => {
                let st = self.stack.borrow();
                let b = self.base.get();
                let frame = Rc::new(st[b..].to_vec());
                Rc::new(OpClosure::Lambda { def: l.clone(), frame, self_slot: None })
            }
        })
    }

    pub fn force_slot(&self, s: Slot, s0: &[Value], s1: &[Value]) -> R<Value> {
        match s {
            Slot::V(v) => Ok(v),
            Slot::Poison(e) => Err(e),
            Slot::Lazy(l) => {
                // call-by-name: evaluated in the *current* state context
                match &*l.code {
                    Node::Var(i) => {
                        return match &s0[*i as usize] {
                            Value::Undef => fail(format!("The variable {} is not assigned a value in the current state.", self.var_name(*i))),
                            v => Ok(v.clone()),
                        }
                    }
                    Node::PrimedVar(i, _) => {
                        return match s1.get(*i as usize) {
                            Some(Value::Undef) | None => fail(format!(
                                "Attempted to evaluate the primed variable {}', which is not yet assigned a value.",
                                self.var_name(*i)
                            )),
                            Some(v) => Ok(v.clone()),
                        }
                    }
                    _ => {}
                }
                if l.cacheable {
                    let (p, n, ep) = (s0.as_ptr() as usize, s0.len(), self.epoch.get());
                    if let Some(c) = l.cache.borrow().iter().find(|c| c.s0_ptr == p && c.s0_len == n && c.epoch == ep) {
                        return Ok(c.val.clone());
                    }
                    let v = self.run_frame_in(&l.frame, &l.substs, &[], &l.code, s0, s1)?;
                    let mut cc = l.cache.borrow_mut();
                    if cc.len() >= 2 {
                        cc.remove(0);
                    }
                    cc.push(LazyCache { s0_ptr: p, s0_len: n, epoch: ep, val: v.clone(), substs: Substs::default() });
                    return Ok(v);
                }
                self.run_frame_in(&l.frame, &l.substs, &[], &l.code, s0, s1)
            }
            Slot::Op(_) => fail("An operator was used where a value was expected."),
            Slot::Memo(m) => Ok(m.v.clone()),
            Slot::Unset => fail("Internal error: use of an unassigned local variable."),
        }
    }

    /// `<Name(p1,p2) line L, col C to line L2, col C2 of module M>`
    pub fn format_label(&self, l: &LabelSpec) -> String {
        let params = if l.base.params.is_empty() {
            String::new()
        } else {
            format!("({})", l.base.params.iter().map(|v| v.to_tla()).collect::<Vec<_>>().join(","))
        };
        let name = &l.base.name;
        match self.node_info.borrow().get(&l.stop) {
            Some(i) => format!("<{}{} line {}, col {} to line {}, col {} of module {}>", name, params, i.loc.bl, i.loc.bc, i.loc.el, i.loc.ec, i.module),
            None => format!("<{}{}>", name, params),
        }
    }

    // ------------------------------------------------------------------ calls

    /// may the value-keyed memo of `d` be used here?  Only while no INSTANCE substitution in scope substitutes a constant `d` reaches.
    #[inline(never)]
    fn dep_memo_scope(&self, d: &CompiledDef) -> bool {
        let ss = self.substs.borrow();
        ss.is_empty()
            || match d.dep_decls.get() {
                Some(ds) => !ss.iter().any(|e| ds.contains(&e.decl)),
                None => false,
            }
    }

    /// `vars == <<x, y, z>>`: building the tuple costs less than the lookups of the state-level caches below (state pointer, variable
    /// values, hash of the values); such a definition is evaluated directly
    #[inline]
    fn cheap_def(d: &CompiledDef) -> bool {
        match d.cheap_body.get() {
            1 => true,
            2 => false,
            _ => Self::classify_cheap_def(d),
        }
    }

    #[inline(never)]
    fn classify_cheap_def(d: &CompiledDef) -> bool {
        fn cheap(n: &Node) -> bool {
            match n {
                Node::Var(_) | Node::PrimedVar(..) | Node::Const(_) => true,
                Node::Tuple(v) => v.len() <= 8 && v.iter().all(|e| cheap(e)),
                _ => false,
            }
        }
        let ok = d.body.borrow().as_ref().map_or(false, |b| cheap(b));
        d.cheap_body.set(if ok { 1 } else { 2 });
        ok
    }

    fn call_def(&self, d: &Rc<CompiledDef>, args: &[Arg], s0: &[Value], s1: &[Value]) -> R<Value> {
        if d.native.get().is_none() {
            let cacheable = d.nparams == 0 && d.level == sem::Level::Const;
            if cacheable {
                if let Some(v) = &*d.cache.borrow() {
                    return Ok(v.clone());
                }
            }
            // a state-level definition without parameters: its value depends only on the state and on the INSTANCE
            // substitutions in scope (the same substitution list object = the same scope)
            let state_cacheable = args.is_empty() && d.nparams == 0 && d.level == sem::Level::State && !Self::cheap_def(d);
            if state_cacheable {
                if let Some(c) = &*d.state_cache.borrow() {
                    if c.s0_ptr == s0.as_ptr() as usize && c.s0_len == s0.len() && c.epoch == self.epoch.get() && c.substs.same(&self.substs.borrow()) {
                        return Ok(c.val.clone());
                    }
                }
                // the variables the definition reads still have the values it was computed with (see `deps`)
                if let Some(deps) = d.deps.get_or_init(|| {
                    crate::deps::state_reads_decls(d).map(|(vars, decls)| {
                        let _ = d.dep_decls.set(decls);
                        Rc::new(vars)
                    })
                }) {
                    if let Some(dc) = &*d.dep_cache.borrow() {
                        if dc.substs.same(&self.substs.borrow())
                            && deps.iter().zip(dc.vals.iter()).all(|(&i, v)| s0.get(i as usize).map_or(false, |x| x.eq_val(v).unwrap_or(false)))
                        {
                            let v = dc.val.clone();
                            *d.state_cache.borrow_mut() = Some(LazyCache { s0_ptr: s0.as_ptr() as usize, s0_len: s0.len(), epoch: self.epoch.get(), val: v.clone(), substs: dc.substs.clone() });
                            return Ok(v);
                        }
                    }
                    // other states with the same values of the variables it reads (a duplicate successor): remembered by value
                    if d.memo_kind.get() != 2 && self.dep_memo_scope(d) {
                        if let Some(v) = dep_memo_get(d, deps, s0) {
                            *d.state_cache.borrow_mut() = Some(LazyCache { s0_ptr: s0.as_ptr() as usize, s0_len: s0.len(), epoch: self.epoch.get(), val: v.clone(), substs: self.substs.borrow().clone() });
                            return Ok(v);
                        }
                    }
                }
            }
            let body = match &*d.body.borrow() {
                Some(b) => b.clone(),
                None => return fail(format!("The definition of {} has no body.", d.name)),
            };
            // the arguments are evaluated in the caller's frame and pushed directly into the callee's frame
            let nb = self.stack.borrow().len();
            for a in args {
                match self.eval_arg(a, s0, s1) {
                    Ok(sl) => self.stack.borrow_mut().push(sl),
                    Err(e) => {
                        self.stack.borrow_mut().truncate(nb);
                        return Err(e);
                    }
                }
            }
            // a pure constant-level operator that builds sets: remembered by the values of its arguments
            let mut memo_key: Option<(u64, Vec<Value>)> = None;
            if d.nparams > 0 && d.level == sem::Level::Const && d.memo_kind.get() != 2 {
                if d.memo_kind.get() == 0 {
                    match crate::memo::memoizable(&d.src) {
                        Some(decls) => {
                            *d.memo_decls.borrow_mut() = decls;
                            d.memo_kind.set(1);
                        }
                        None => d.memo_kind.set(2),
                    }
                }
                // an enclosing INSTANCE may substitute a constant the operator reaches: then the value is not a function of the arguments
                let substs_ok = {
                    let ss = self.substs.borrow();
                    ss.is_empty()
                        || match &*d.memo_decls.borrow() {
                            Some(ds) => !ss.iter().any(|e| ds.contains(&e.decl)),
                            None => false,
                        }
                };
                if d.memo_kind.get() == 1 && substs_ok {
                    // the arguments are hashed and compared where they are (the callee's frame); they are copied only for a new entry
                    let key = {
                        let st = self.stack.borrow();
                        let mut h = Hasher::new();
                        let ok = st[nb..].iter().all(|s| matches!(s, Slot::V(v) if v.hash_is_cheap() && v.hash_into(&mut h).is_ok()));
                        if ok {
                            Some(h.finish())
                        } else {
                            None
                        }
                    };
                    d.memo_calls.set(d.memo_calls.get() + 1);
                    if let Some(key) = key {
                        let hit = {
                            let st = self.stack.borrow();
                            let a1 = &st[nb..];
                            d.memo.borrow().get(&key).and_then(|bucket| {
                                bucket
                                    .iter()
                                    .find(|(a, _)| a.len() == a1.len() && a.iter().zip(a1.iter()).all(|(x, y)| matches!(y, Slot::V(yv) if x.eq_val(yv).unwrap_or(false))))
                                    .map(|(_, r)| r.clone())
                            })
                        };
                        if let Some(r) = hit {
                            d.memo_hits.set(d.memo_hits.get() + 1);
                            self.stack.borrow_mut().truncate(nb);
                            return Ok(r);
                        }
                    }
                    if d.memo_calls.get() >= 128 && d.memo_hits.get() * 2 < d.memo_calls.get() {
                        // the arguments hardly ever repeat (or cannot be hashed): hashing them costs more than it saves
                        d.memo_kind.set(2);
                        d.memo.borrow_mut().clear();
                    } else if let Some(key) = key {
                        let vals: Vec<Value> = self.stack.borrow()[nb..].iter().map(|s| if let Slot::V(v) = s { v.clone() } else { Value::Undef }).collect();
                        memo_key = Some((key, vals));
                    }
                }
            }
            let nslots = d.nslots.get().max(args.len());
            grow_unset(&mut self.stack.borrow_mut(), nb + nslots);
            let old = self.base.get();
            self.base.set(nb);
            self.depth.set(self.depth.get() + 1);
            #[cfg(feature = "prof")]
            let prev_def = PROF_DEF.swap(Rc::as_ptr(d) as usize, std::sync::atomic::Ordering::Relaxed);
            let r = if self.depth.get() > MAX_DEPTH {
                fail_code(crate::ec::SYSTEM_STACK_OVERFLOW, "Java StackOverflowError: the evaluation recursed too deeply")
            } else {
                self.eval(&body, s0, s1)
            };
            #[cfg(feature = "prof")]
            PROF_DEF.store(prev_def, std::sync::atomic::Ordering::Relaxed);
            self.depth.set(self.depth.get() - 1);
            self.stack.borrow_mut().truncate(nb);
            self.base.set(old);
            let mut v = r?;
            if let Some((key, vals)) = memo_key {
                if let Ok(nv) = v.normalize() {
                    v = nv;
                    if d.memo_n.get() >= 20_000 {
                        d.memo.borrow_mut().clear();
                        d.memo_n.set(0);
                    }
                    d.memo.borrow_mut().entry(key).or_default().push((vals, v.clone()));
                    d.memo_n.set(d.memo_n.get() + 1);
                }
            }
            if cacheable {
                *d.cache.borrow_mut() = Some(v.clone());
            }
            if state_cacheable {
                *d.state_cache.borrow_mut() = Some(LazyCache { s0_ptr: s0.as_ptr() as usize, s0_len: s0.len(), epoch: self.epoch.get(), val: v.clone(), substs: self.substs.borrow().clone() });
                if let Some(Some(deps)) = d.deps.get() {
                    if deps.iter().all(|&i| (i as usize) < s0.len()) {
                        let vals: Vec<Value> = deps.iter().map(|&i| s0[i as usize].clone()).collect();
                        if d.memo_kind.get() != 2 && self.dep_memo_scope(d) {
                            dep_memo_put(d, deps, s0, &v);
                        }
                        *d.dep_cache.borrow_mut() = Some(DepCache { vals, val: v.clone(), substs: self.substs.borrow().clone() });
                    }
                }
            }
            return Ok(v);
        }
        if let Some(f) = d.native.get() {
            // hot pure natives take their (ordinary, state-level) arguments as plain values
            match d.fast.get() {
                crate::natives::Fast::F1(g) if args.len() == 1 => {
                    if let Arg::Val(e, false) = &args[0] {
                        // a read path over the state (`Len(net[p][q])`) is passed by reference
                        let xo;
                        let x: &Value = match self.place(e, s0) {
                            Some(p) => p,
                            None => {
                                xo = self.eval(e, s0, s1)?;
                                &xo
                            }
                        };
                        return g(x);
                    }
                }
                crate::natives::Fast::F2(g) if args.len() == 2 => {
                    if let (Arg::Val(e0, false), Arg::Val(e1, false)) = (&args[0], &args[1]) {
                        let xo;
                        let x: &Value = match self.place(e0, s0) {
                            Some(p) => p,
                            None => {
                                xo = self.eval(e0, s0, s1)?;
                                &xo
                            }
                        };
                        let yo;
                        let y: &Value = match self.place(e1, s0) {
                            Some(p) => p,
                            None => {
                                yo = self.eval(e1, s0, s1)?;
                                &yo
                            }
                        };
                        return g(x, y);
                    }
                }
                _ => {}
            }
            let mut slots: Vec<Slot> = self.slot_pool.borrow_mut().pop().unwrap_or_default();
            for a in args {
                match self.eval_arg(a, s0, s1) {
                    Ok(sl) => slots.push(sl),
                    Err(e) => {
                        slots.clear();
                        self.slot_pool.borrow_mut().push(slots);
                        return Err(e);
                    }
                }
            }
            let r = f(self, &mut slots, s0, s1).map_err(|e| crate::natives::wrap_override_error(&d.src.original().module, &d.name, e));
            slots.clear();
            self.slot_pool.borrow_mut().push(slots);
            return r;
        }
        let mut slots: Vec<Slot> = Vec::with_capacity(args.len());
        for a in args {
            slots.push(self.eval_arg(a, s0, s1)?);
        }
        self.call_def_slots(d, slots, s0, s1)
    }

    pub fn call_def_slots(&self, d: &Rc<CompiledDef>, mut slots: Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
        if let Some(f) = d.native.get() {
            return f(self, &mut slots, s0, s1).map_err(|e| crate::natives::wrap_override_error(&d.src.original().module, &d.name, e));
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
        if let OpClosure::Lambda { def, frame, self_slot } = &**c {
            if args.len() <= 4 {
                // the arguments are evaluated in the caller's frame, then moved into the LAMBDA's frame (no vectors)
                let mut a: [Slot; 4] = [Slot::Unset, Slot::Unset, Slot::Unset, Slot::Unset];
                for (i, x) in args.iter().enumerate() {
                    a[i] = self.eval_arg(x, s0, s1)?;
                }
                return self.run_lambda(c, def, frame, *self_slot, &mut a[..args.len()], s0, s1);
            }
        }
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
            OpClosure::Lambda { def, frame, self_slot } if slots.len() <= 4 => {
                let mut slots = slots;
                self.run_lambda(c, def, frame, *self_slot, &mut slots[..], s0, s1)
            }
            OpClosure::Lambda { def, frame, self_slot } => {
                // runs right now in the current state: no need to copy the states into a `Captured`
                let substs = self.substs.borrow().clone();
                let cap = Captured { frame: frame.clone(), substs, s0: self.no_state.clone(), s1: self.no_state.clone() };
                // parameters occupy consecutive slots starting at `def.nslots`
                let mut assigns: Vec<(u32, Slot)> = slots.into_iter().enumerate().map(|(i, s)| ((def.nslots + i) as u32, s)).collect();
                if let Some(ss) = self_slot {
                    assigns.push((*ss, Slot::Op(c.clone())));
                }
                self.run_captured_in(&cap, &assigns, &def.body, s0, s1)
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
            // Java: `new SubsetValue(arg)` does not look at the argument
            B::Subset => Ok(Value::Subset(Rc::new(vals[0].clone()))),
            B::UnionAll => {
                if !vals[0].is_set_like() {
                    return fail(format!("Attempted to apply UNION to the non-set value\n{}", vals[0].to_tla()));
                }
                if let Some(r) = union_unnormalized(&vals[0]) {
                    return r;
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
                if let Some(r) = reduce_unnormalized(b, &vals[0], &vals[1]) {
                    return r;
                }
                // Java: Tool.eval OPCODE_cup: an empty enumerated set (`Reducible.cup`) leaves the other operand as it is
                if b == B::Union {
                    let is_empty = |v: &Value| matches!(v, Value::Set(s) if s.is_empty()) || matches!(v, Value::Interval(lo, hi) if hi < lo);
                    if is_empty(&vals[0]) {
                        return Ok(vals[1].clone());
                    }
                    if is_empty(&vals[1]) {
                        return Ok(vals[0].clone());
                    }
                }
                // two normalized sets: one merge (`Value::merge_sets`); a failing comparison takes the general path below
                if let (Value::Set(x), Value::Set(y)) = (&vals[0], &vals[1]) {
                    let op = match b {
                        B::Union => SetOp::Cup,
                        B::Intersect => SetOp::Cap,
                        _ => SetOp::Diff,
                    };
                    if let Some(v) = merge_sets(op, x, y) {
                        return Ok(Value::Set(Rc::new(v)));
                    }
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

    #[inline(always)]
    pub fn eval(&self, e: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        #[cfg(feature = "prof")]
        {
            if PROF_ON.load(std::sync::atomic::Ordering::Relaxed) {
                let prev = PROF_CUR.swap(Rc::as_ptr(e) as usize, std::sync::atomic::Ordering::Relaxed);
                let r = self.eval_inner(e, s0, s1);
                PROF_CUR.store(prev, std::sync::atomic::Ordering::Relaxed);
                return r;
            }
        }
        // leaves are handled inline: `eval_inner` has a large stack frame and a long prologue
        match &**e {
            Node::Const(v) => return Ok(v.clone()),
            Node::Var(i) => {
                if let Some(v) = s0.get(*i as usize) {
                    if !matches!(v, Value::Undef) {
                        return Ok(v.clone());
                    }
                }
            }
            Node::Local(i) => {
                if let Slot::V(v) = &self.stack.borrow()[self.base.get() + *i as usize] {
                    return Ok(v.clone());
                }
            }
            _ => {}
        }
        self.eval_inner(e, s0, s1)
    }

    /// `a = b` / `a # b`.  A left operand that is a read path over the state is compared in place (no clone / drop):
    /// `eval_eq_placed`.  Kept out of `eval_inner` so that its stack frame stays small; the other operands take the plain code.
    #[inline(never)]
    fn eval_eq(&self, a: &Ex, b: &Ex, neg: bool, s0: &[Value], s1: &[Value]) -> R<Value> {
        if matches!(&**a, Node::Var(_) | Node::FcnApply(..)) {
            return self.eval_eq_placed(a, b, neg, s0, s1);
        }
        let x = self.eval(a, s0, s1)?;
        // a constant right-hand side is compared in place (no clone / drop of the constant)
        if let Node::Const(c) = &**b {
            return Ok(Value::Bool(x.eq_val(c)? != neg));
        }
        let y = self.eval(b, s0, s1)?;
        Ok(Value::Bool(x.eq_val(&y)? != neg))
    }

    #[inline(never)]
    fn eval_eq_placed(&self, a: &Ex, b: &Ex, neg: bool, s0: &[Value], s1: &[Value]) -> R<Value> {
        let xo;
        let x: &Value = match self.place(a, s0) {
            Some(p) => p,
            None => {
                xo = self.eval(a, s0, s1)?;
                &xo
            }
        };
        if let Node::Const(c) = &**b {
            return Ok(Value::Bool(x.eq_val(c)? != neg));
        }
        if matches!(&**b, Node::Var(_) | Node::FcnApply(..)) {
            if let Some(y) = self.place(b, s0) {
                return Ok(Value::Bool(x.eq_val(y)? != neg));
            }
        }
        let y = self.eval(b, s0, s1)?;
        Ok(Value::Bool(x.eq_val(&y)? != neg))
    }

    /// `a \in b` / `a \notin b` (a left operand that is a read path over the state: `eval_in_placed`)
    #[inline(never)]
    fn eval_in(&self, a: &Ex, b: &Ex, neg: bool, s0: &[Value], s1: &[Value]) -> R<Value> {
        if matches!(&**a, Node::Var(_) | Node::FcnApply(..)) {
            return self.eval_in_placed(a, b, neg, s0, s1);
        }
        let x = self.eval(a, s0, s1)?;
        self.in_rhs(&x, b, neg, s0, s1)
    }

    #[inline(never)]
    fn eval_in_placed(&self, a: &Ex, b: &Ex, neg: bool, s0: &[Value], s1: &[Value]) -> R<Value> {
        let xo;
        let x: &Value = match self.place(a, s0) {
            Some(p) => p,
            None => {
                xo = self.eval(a, s0, s1)?;
                &xo
            }
        };
        self.in_rhs(x, b, neg, s0, s1)
    }

    /// `x \in b`: a constant or a state variable as the set is used in place
    #[inline(always)]
    fn in_rhs(&self, x: &Value, b: &Ex, neg: bool, s0: &[Value], s1: &[Value]) -> R<Value> {
        match &**b {
            Node::Const(c) => return Ok(Value::Bool(c.member(x)? != neg)),
            Node::Var(i) => {
                if let Some(v) = s0.get(*i as usize) {
                    if !matches!(v, Value::Undef) {
                        return Ok(Value::Bool(v.member(x)? != neg));
                    }
                }
            }
            _ => {}
        }
        let y = self.eval(b, s0, s1)?;
        Ok(Value::Bool(y.member(x)? != neg))
    }

    /// `r.field` (a record that is a read path over the state is not cloned: `eval_record_placed`)
    #[inline(never)]
    fn eval_record(&self, r: &Ex, field: u32, s0: &[Value], s1: &[Value]) -> R<Value> {
        if matches!(&**r, Node::Var(_) | Node::FcnApply(..)) {
            if let Some(rv) = self.place(r, s0) {
                return Self::record_field(rv, field);
            }
        }
        let rv = self.eval(r, s0, s1)?;
        Self::record_field(&rv, field)
    }

    fn record_field(rv: &Value, field: u32) -> R<Value> {
        match rv {
            Value::Fcn(f) => {
                for (d, v) in f.dom.iter().zip(f.vals.iter()) {
                    if let Value::Str(id) = d {
                        if *id == field {
                            return Ok(v.clone());
                        }
                    }
                }
                fail(format!("Attempted to access nonexistent field '{}' of record\n{}", intern::name_of(field), rv.to_tla()))
            }
            Value::FcnLam(_) => rv.apply(&Value::Str(field)),
            _ => fail(format!("Attempted to access field '{}' of the non-record value\n{}", intern::name_of(field), rv.to_tla())),
        }
    }

    /// The value of a pure read path over the current state (`x`, `x[a]`, `x[a][b]`, ... with constant, frame-slot or state-variable
    /// arguments) as a reference into `s0`: no clone / drop per step.  `None` = not such a path, or a step does not apply (outside the
    /// domain, lazy function, ...): the caller evaluates the expression the normal way, which yields the value or the error.
    fn place<'a>(&self, e: &Ex, s0: &'a [Value]) -> Option<&'a Value> {
        match &**e {
            Node::Var(i) => match s0.get(*i as usize) {
                Some(Value::Undef) | None => None,
                Some(v) => Some(v),
            },
            Node::FcnApply(f, a) => {
                let base = self.place(f, s0)?;
                match &**a {
                    Node::Const(v) => base.apply_ref(v),
                    Node::Local(i) => match &self.stack.borrow()[self.base.get() + *i as usize] {
                        Slot::V(v) => base.apply_ref(v),
                        _ => None,
                    },
                    Node::Var(i) => match s0.get(*i as usize) {
                        Some(Value::Undef) | None => None,
                        Some(v) => base.apply_ref(v),
                    },
                    Node::FcnApply(..) => {
                        let av = self.place(a, s0)?;
                        base.apply_ref(av)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Java: `CallStack.toString`: `0. Line .., column .. to line .., column .. in Module` for the expressions the error passed, outermost first;
    /// consecutive identical nodes are skipped
    pub fn call_stack_text(&self, e: &TlcErr) -> String {
        self.call_stack_text_ext(e, &[])
    }

    /// like `call_stack_text` with more nodes after the frames (Java: `CallStack.freeze(FingerprintException)` pushes the sources of the values)
    pub fn call_stack_text_ext(&self, e: &TlcErr, extra: &[usize]) -> String {
        let ni = self.node_info.borrow();
        let mut out = String::new();
        let mut last: Option<String> = None;
        let mut depth = 0;
        if std::env::var_os("TLCRS_DBG_FRAMES").is_some() {
            for p in e.frames.iter().rev() {
                match ni.get(p) {
                    Some(i) => eprintln!("FRAME {:x} {}:{}-{}:{} {} syn={}", p, i.loc.bl, i.loc.bc, i.loc.el, i.loc.ec, i.module, i.synthetic),
                    None => eprintln!("FRAME {:x} (no info)", p),
                }
            }
        }
        for p in e.frames.iter().rev().chain(extra.iter()) {
            if let Some(i) = ni.get(p).filter(|i| !i.synthetic) {
                let l = format!("Line {}, column {} to line {}, column {} in {}", i.loc.bl, i.loc.bc, i.loc.el, i.loc.ec, i.module);
                if last.as_deref() == Some(l.as_str()) {
                    continue;
                }
                out.push_str(&format!("{}. {}\n", depth, l));
                depth += 1;
                last = Some(l);
            }
        }
        if depth == 0 {
            return "    The error call stack is empty.\n".to_string();
        }
        out.push('\n');
        out
    }

    /// Java: `CallStackTool` (`Tool.setCallStack`): run `f` with every evaluation recording the nodes a failure passes (`TlcErr::frames`).
    /// Tracking is off otherwise: the normal run does not pay for the call stack, a failure that needs it is replayed (as TLC does).
    pub fn with_tracking<T>(&self, f: impl FnOnce() -> T) -> T {
        let was = self.tracking.replace(true);
        self.track_skip.set(false);
        let r = f();
        self.tracking.set(was);
        self.track_skip.set(false);
        r
    }

    /// `with_tracking` that drops what the evaluation printed (the replay shows no output of its own)
    pub fn tracked_quiet<T>(&self, f: impl FnOnce() -> T) -> T {
        let out_len = self.out.borrow().len();
        let r = self.with_tracking(f);
        let mut out = self.out.borrow_mut();
        let keep = out_len.min(out.len());
        out.truncate(keep);
        r
    }

    /// Java: the replay with the call-stack tool after a failure: `f` repeats the evaluation that failed with `e`; the failure of the
    /// replay (the same one, now carrying the nodes it passed) is returned. The output of the replay is dropped. A failure that is not
    /// reproduced is returned as it was (without a call stack).
    pub fn replay<T>(&self, e: Box<TlcErr>, f: impl FnOnce() -> R<T>) -> Box<TlcErr> {
        // Java: a StackOverflowError is not replayed (`keepCallStack` is false)
        if self.tracking.get() || !e.frames.is_empty() || e.not_ported || e.code == crate::ec::SYSTEM_STACK_OVERFLOW {
            return e;
        }
        let r = self.tracked_quiet(f);
        match r {
            Err(e2) => e2,
            Ok(_) => e,
        }
    }

    /// the tracked variant of `eval_inner` (only while a failure is replayed, see `Ev::replay`): the expression being evaluated is on the
    /// stack of an error that leaves it
    #[cold]
    #[inline(never)]
    fn eval_tracked(&self, e: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        self.track_skip.set(true);
        let mut r = self.eval_inner(e, s0, s1);
        if let Err(er) = &mut r {
            push_frame(er, Rc::as_ptr(e) as usize);
        }
        r
    }

    /// Java: `CallStackTool`: the expression being evaluated is on the stack of an error that leaves it. (Kept out of `eval`, which is
    /// inlined at every call site: the check there costs about 10 % on the evaluator-bound models.)
    #[inline(never)]
    pub fn eval_inner(&self, e: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        if self.tracking.get() && !self.track_skip.replace(false) {
            return self.eval_tracked(e, s0, s1);
        }
        match &**e {
            Node::Const(v) => Ok(v.clone()),
            Node::Local(i) => {
                let s = self.get_slot(*i);
                self.force_slot(s, s0, s1)
            }
            Node::Var(i) => match &s0[*i as usize] {
                Value::Undef => fail(format!("The variable {} is not assigned a value in the current state.", self.var_name(*i))),
                v => Ok(v.clone()),
            },
            Node::PrimedVar(i, at) => match s1.get(*i as usize) {
                // Java: `ENABLED` evaluates `x'` by evaluating `x` in the successor under construction; an unassigned `x` is an
                // undefined identifier (Tool.evalApplImpl), not an error that says that the successor is not specified
                Some(Value::Undef) | None if self.enabled_depth.get() > 0 => {
                    let loc = match at {
                        Some(a) => format!("line {}, col {} to line {}, col {} of module {}", a.0.bl, a.0.bc, a.0.el, a.0.ec, a.1),
                        None => String::new(),
                    };
                    fail_code(
                        crate::ec::TLC_CONFIG_UNDEFINED_OR_NO_OPERATOR,
                        format!("@!@!@STARTMSG 2280:0 @!@!@\nIn evaluation, the identifier {} is either undefined or not an operator.\n{}\n@!@!@ENDMSG 2280 @!@!@", self.var_name(*i), loc),
                    )
                }
                Some(Value::Undef) | None => fail(format!(
                    "Attempted to evaluate the primed variable {}', which is not yet assigned a value.",
                    self.var_name(*i)
                )),
                Some(v) => Ok(v.clone()),
            },
            Node::Decl(dr) => {
                if self.enabled_depth.get() > 0 && s0.as_ptr() as usize == self.virt_ptr.get() {
                    if let Some((_, v)) = self.virt.borrow().iter().find(|(id, _)| *id == dr.id) {
                        return Ok(v.clone());
                    }
                }
                {
                    let ss = self.substs.borrow();
                    for ent in ss.iter() {
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
                    let d0 = self.const_ops.borrow().get(&dr.id).cloned();
                    if let Some(d) = d0 {
                        return self.call_def(&d, &[], s0, s1);
                    }
                    match self.consts.borrow().get(&dr.id) {
                        Some(v) => Ok(v.clone()),
                        None => fail_code(
                            crate::ec::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM,
                            format!("The constant parameter {} is not assigned a value by the configuration file.", dr.name),
                        ),
                    }
                }
            }
            Node::Prime(inner) => {
                let empty = self.empty();
                self.prime_depth.set(self.prime_depth.get() + 1);
                let r = self.eval(inner, s1, &empty);
                self.prime_depth.set(self.prime_depth.get() - 1);
                r
            }
            Node::Unchanged(inner) => {
                let cur = self.eval(inner, s0, s1)?;
                let empty = self.empty();
                let nxt = self.eval(inner, s1, &empty)?;
                Ok(Value::Bool(cur.eq_val(&nxt)?))
            }
            Node::Fold(inner, cache) => {
                if let Some(v) = &*cache.borrow() {
                    return Ok(v.clone());
                }
                let v = self.eval(inner, s0, s1)?;
                *cache.borrow_mut() = Some(v.clone());
                Ok(v)
            }
            Node::Arith(op, a, b, nf) => {
                let x = self.eval(a, s0, s1)?;
                let y = self.eval(b, s0, s1)?;
                if let (Value::Int(p), Value::Int(q)) = (&x, &y) {
                    let (p, q) = (*p, *q);
                    match op {
                        ArithOp::Plus => {
                            if let Some(r) = p.checked_add(q) {
                                return Ok(Value::Int(r));
                            }
                        }
                        ArithOp::Minus => {
                            if let Some(r) = p.checked_sub(q) {
                                return Ok(Value::Int(r));
                            }
                        }
                        ArithOp::Times => {
                            if let Some(r) = p.checked_mul(q) {
                                return Ok(Value::Int(r));
                            }
                        }
                        ArithOp::Lt => return Ok(Value::Bool(p < q)),
                        ArithOp::Gt => return Ok(Value::Bool(p > q)),
                        ArithOp::Le => return Ok(Value::Bool(p <= q)),
                        ArithOp::Ge => return Ok(Value::Bool(p >= q)),
                        ArithOp::DotDot => return Ok(Value::Interval(p, q)),
                        // the natives (`Naturals.%`, `\div`, `^`) handle the error cases: a non-positive modulus, a zero divisor, a
                        // negative exponent, `0^0` and an overflow fall through to them with the evaluated values
                        ArithOp::Mod => {
                            if q > 0 {
                                let r = p % q;
                                return Ok(Value::Int(if r < 0 { r + q } else { r }));
                            }
                        }
                        ArithOp::Div => {
                            if q != 0 {
                                // Java: `Naturals.IntegerDivision`: truncating division corrected towards minus infinity
                                let mut d = p.wrapping_div(q);
                                if d < 0 && d.wrapping_mul(q) != p {
                                    d -= 1;
                                }
                                return Ok(Value::Int(d));
                            }
                        }
                        ArithOp::Pow => {
                            if q >= 0 && !(p == 0 && q == 0) {
                                if let Some(r) = p.checked_pow(q as u32) {
                                    return Ok(Value::Int(r));
                                }
                            }
                        }
                    }
                }
                nf(self, &mut vec![Slot::V(x), Slot::V(y)], s0, s1)
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
            Node::LetScope(slots, body) => {
                for s in slots {
                    self.set_slot(*s, Slot::Unset);
                }
                self.eval(body, s0, s1)
            }
            Node::LetUse(slot, def) => {
                let (p, n, ep) = (s0.as_ptr() as usize, s0.len(), self.epoch.get());
                if let Slot::Memo(m) = &self.stack.borrow()[self.base.get() + *slot as usize] {
                    if m.ptr == p && m.len == n && m.epoch == ep {
                        return Ok(m.v.clone());
                    }
                }
                let v = self.eval(def, s0, s1)?;
                self.set_slot(*slot, Slot::Memo(Rc::new(MemoVal { v: v.clone(), ptr: p, len: n, epoch: self.epoch.get() })));
                Ok(v)
            }
            Node::Bi(b, es) => {
                let r = self.eval_bi(*b, es, s0, s1);
                if matches!(b, B::Subset | B::Times) {
                    if let Ok(v) = &r {
                        note_source(v, Rc::as_ptr(e) as usize);
                    }
                }
                r
            }
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
            Node::Eq(a, b) => self.eval_eq(a, b, false, s0, s1),
            Node::Neq(a, b) => self.eval_eq(a, b, true, s0, s1),
            Node::In(a, b) => self.eval_in(a, b, false, s0, s1),
            Node::NotIn(a, b) => self.eval_in(a, b, true, s0, s1),
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
                Value::set_lit(v)
            }
            Node::FcnApply(f, a) => {
                // `x[a][b]...`: every step is a reference into the state, only the result is cloned
                if matches!(&**f, Node::FcnApply(..)) {
                    if let Some(v) = self.place(e, s0) {
                        return Ok(v.clone());
                    }
                }
                // a state variable or a constant is applied in place (no reference-count traffic): the argument is evaluated
                // first (a variable or constant read has no effect and cannot fail on its own)
                match &**f {
                    Node::Var(i) => {
                        if let Some(fv) = s0.get(*i as usize) {
                            if !matches!(fv, Value::Undef) {
                                let av = self.eval(a, s0, s1)?;
                                return fv.apply(&av);
                            }
                        }
                    }
                    Node::Const(fv) => {
                        let av = self.eval(a, s0, s1)?;
                        return fv.apply(&av);
                    }
                    _ => {}
                }
                let fv = self.eval(f, s0, s1)?;
                let av = self.eval(a, s0, s1)?;
                fv.apply(&av)
            }
            Node::Record(r, field) => self.eval_record(r, *field, s0, s1),
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
            // large arms live in `eval_heavy` so that this hot, recursive function keeps a small stack frame
            Node::CallDecl(..) | Node::LetRec(..) | Node::Times(..) | Node::SubsetOf{ .. } | Node::SetOfAll(..) | Node::FcnCons(..) | Node::SetOfFcns(..) | Node::RcdCons(..) | Node::SetOfRcds(..) | Node::Except(..) | Node::ActionSub { .. } | Node::Choose(..) | Node::SubstIn(..) | Node::Temporal(..) | Node::Unsupported(..) | Node::Fail(..) | Node::Memo(..) => self.eval_heavy(e, s0, s1),
        }
    }

    /// `Node::Memo`: the value of a pure expression for the values of the variables / slots it reads
    fn eval_memo(&self, m: &MemoNode, s0: &[Value], s1: &[Value]) -> R<Value> {
        if m.off.get() {
            return self.eval(&m.inner, s0, s1);
        }
        // the free slots must hold plain values (not call-by-name arguments, operators, lazy sets or functions)
        let mut sl: [Value; 4] = [Value::Undef, Value::Undef, Value::Undef, Value::Undef];
        {
            let st = self.stack.borrow();
            let b = self.base.get();
            for (k, &s) in m.slots.iter().enumerate() {
                match st.get(b + s as usize) {
                    Some(Slot::V(v)) if memo_key_value(v) => sl[k] = v.clone(),
                    _ => {
                        drop(st);
                        return self.eval(&m.inner, s0, s1);
                    }
                }
            }
        }
        let nsl = m.slots.len();
        let same = |a: &Value, b: &Value| a.eq_val(b).unwrap_or(false);
        let cur_substs = self.substs.borrow().clone();
        m.calls.set(m.calls.get() + 1);
        {
            let cache = m.cache.borrow();
            for e in cache.iter() {
                if e.substs.same(&cur_substs)
                    && m.v0.iter().zip(e.a0.iter()).all(|(&i, v)| s0.get(i as usize).map_or(false, |x| same(x, v)))
                    && m.v1.iter().zip(e.a1.iter()).all(|(&i, v)| s1.get(i as usize).map_or(false, |x| same(x, v)))
                    && (0..nsl).all(|k| same(&sl[k], &e.sl[k]))
                {
                    m.hits.set(m.hits.get() + 1);
                    return Ok(e.val.clone());
                }
            }
        }
        if m.calls.get() >= 64 && m.hits.get() * 4 < m.calls.get() {
            // the values it reads hardly ever repeat: remembering them costs more than it saves
            m.off.set(true);
            m.cache.borrow_mut().clear();
            return self.eval(&m.inner, s0, s1);
        }
        let v = self.eval(&m.inner, s0, s1)?;
        let a0: Option<Vec<Value>> = m.v0.iter().map(|&i| s0.get(i as usize).cloned()).collect();
        let a1: Option<Vec<Value>> = m.v1.iter().map(|&i| s1.get(i as usize).cloned()).collect();
        if let (Some(a0), Some(a1)) = (a0, a1) {
            if !a0.iter().chain(a1.iter()).any(|x| matches!(x, Value::Undef)) {
                let mut cache = m.cache.borrow_mut();
                if cache.len() >= 4 {
                    cache.remove(0);
                }
                cache.push(MemoEntry { a0, a1, sl: sl[..nsl].to_vec(), substs: cur_substs, val: v.clone() });
            }
        }
        Ok(v)
    }

    #[inline(never)]
    fn eval_heavy(&self, e: &Ex, s0: &[Value], s1: &[Value]) -> R<Value> {
        match &**e {
            Node::Memo(m) => self.eval_memo(m, s0, s1),
            Node::CallDecl(dr, args) => {
                {
                    let ss = self.substs.borrow();
                    for ent in ss.iter() {
                        if ent.decl == dr.id {
                            if let Slot::Op(c) = ent.slot.clone() {
                                drop(ss);
                                return self.apply_closure(&c, args, s0, s1);
                            }
                            break;
                        }
                    }
                }
                let table = self.const_tables.borrow().get(&dr.id).cloned();
                if let Some(table) = table {
                    // Java: OpRcdValue.eval
                    let mut vals = Vec::with_capacity(args.len());
                    for a in args {
                        let sl = self.eval_arg(a, s0, s1)?;
                        vals.push(self.force_slot(sl, s0, s1)?);
                    }
                    for (dom, v) in table.iter() {
                        if dom.len() != vals.len() {
                            return fail(format!("Attempted to apply the operator {}
with wrong number of arguments.", dr.name));
                        }
                        let mut matched = true;
                        for (x, y) in dom.iter().zip(vals.iter()) {
                            if !x.eq_val(y)? {
                                matched = false;
                                break;
                            }
                        }
                        if matched {
                            return Ok(v.clone());
                        }
                    }
                    let shown: Vec<String> = vals.iter().map(|v| v.to_tla()).collect();
                    return fail(format!("Attempted to apply operator:
{}
to arguments ({}), which is undefined.", dr.name, shown.join(", ")));
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
            Node::LetRec(defs, body) => {
                for (slot, l) in defs {
                    let frame = {
                        let st = self.stack.borrow();
                        Rc::new(st[self.base.get()..].to_vec())
                    };
                    let clo = Rc::new(OpClosure::Lambda { def: l.clone(), frame, self_slot: Some(*slot) });
                    self.set_slot(*slot, Slot::Op(clo));
                }
                self.eval(body, s0, s1)
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
                let r = Value::SetOfTuples(Rc::new(v));
                note_source(&r, Rc::as_ptr(e) as usize);
                Ok(r)
            }
            Node::SubsetOf { bound, pred, .. } => {
                let base = self.eval(&bound.set, s0, s1)?;
                if !base.is_set_like() {
                    return fail(format!("Attempted to construct a set of the form {{x \\in S : P}} where S is not a set:\n{}", base.to_tla()));
                }
                // Java: SetPredValue is always lazy; small materialized bases are filtered eagerly (cheaper than a capture)
                let small = match &base {
                    Value::Set(_) | Value::SetU(_) => true,
                    Value::Interval(lo, hi) => hi.saturating_sub(*lo) < 100_000,
                    _ => false,
                };
                if small {
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
            Node::FcnCons(bounds, body, self_slot, pure_body) => {
                if bounds.len() == 1 {
                    let b = &bounds[0];
                    let dom = self.eval(&b.set, s0, s1)?;
                    if !dom.is_set_like() {
                        return fail(format!("Attempted to construct a function over the non-set value\n{}", dom.to_tla()));
                    }
                    // A function over a small domain whose body only reads the states is computed right away instead of
                    // capturing the frame and both states for a lazy `FcnLambdaValue` (the value is the same; if the body
                    // fails for some element the lazy function is built as usual, so errors still show up when it is used).
                    if self_slot.is_none() && !b.tuple && b.nvars == 1 && *pure_body.get_or_init(|| crate::deps::is_pure_state_expr(body)) {
                        let elems: Option<Rc<Vec<Value>>> = match &dom {
                            Value::Set(v) if v.len() <= 16 => Some(v.clone()),
                            Value::Interval(lo, hi) if (*hi as i64) - (*lo as i64) < 16 => Some(Rc::new((*lo..=*hi).map(Value::Int).collect())),
                            _ => None,
                        };
                        if let Some(elems) = elems {
                            let mut vals = Vec::with_capacity(elems.len());
                            let mut complete = true;
                            for el in elems.iter() {
                                self.bind_bound(b, el)?;
                                match self.eval(body, s0, s1) {
                                    Ok(v) => vals.push(v),
                                    Err(_) => {
                                        complete = false;
                                        break;
                                    }
                                }
                            }
                            if complete {
                                return Ok(Value::fcn_sorted(elems.to_vec(), vals));
                            }
                        }
                    }
                    let cap = self.capture(s0, s1);
                    let ev = self.rc();
                    let (slot, nvars, tuple) = (b.slot, b.nvars, b.tuple);
                    let body = body.clone();
                    let me: Rc<RefCell<Option<Value>>> = Rc::new(RefCell::new(None));
                    let me2 = me.clone();
                    let self_slot = *self_slot;
                    let lir = Rc::new(LamIr { cap: cap.clone(), binds: vec![(slot, nvars, tuple)], body: body.clone(), self_slot, me: me.clone() });
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
                        body: Some(lir),
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
                    let lir = Rc::new(LamIr {
                        cap: cap.clone(),
                        binds: slots.clone(),
                        body: body.clone(),
                        self_slot,
                        me: me.clone(),
                    });
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
                        body: Some(lir),
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
                let v = Value::SetOfFcns(Rc::new((d, r)));
                note_source(&v, Rc::as_ptr(e) as usize);
                Ok(v)
            }
            Node::RcdCons(fields, dom, pos) => {
                // the fields are evaluated in the order written; the values are stored in the order of the shared domain
                if fields.is_empty() {
                    return Ok(Value::record(vec![]));
                }
                let mut vals = vec![Value::Undef; fields.len()];
                for (i, (_, x)) in fields.iter().enumerate() {
                    vals[pos[i]] = self.eval(x, s0, s1)?;
                }
                Ok(Value::Fcn(Rc::new(Fcn::new(dom.clone(), vals))))
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
                let r = Value::SetOfRcds(Rc::new(v));
                note_source(&r, Rc::as_ptr(e) as usize);
                Ok(r)
            }
            Node::Except(f, specs, floc) => {
                let mut cur = self.eval(f, s0, s1)?;
                // fast path: `[f EXCEPT ![i] = e]`
                if specs.len() == 1 && specs[0].path.len() == 1 {
                    if let PathIr::Index(x) = &specs[0].path[0] {
                        let arg = self.eval(x, s0, s1)?;
                        return self.except_path(cur, std::slice::from_ref(&arg), 0, &specs[0], s0, s1, floc);
                    }
                }
                for sp in specs {
                    // the path (at most 4 steps without an allocation)
                    let mut small: [Value; 4] = [Value::Undef, Value::Undef, Value::Undef, Value::Undef];
                    let mut big: Vec<Value> = Vec::new();
                    let n = sp.path.len();
                    for (j, p) in sp.path.iter().enumerate() {
                        let v = match p {
                            PathIr::Field(n) => Value::Str(*n),
                            PathIr::Index(x) => self.eval(x, s0, s1)?,
                        };
                        if n <= 4 {
                            small[j] = v;
                        } else {
                            big.push(v);
                        }
                    }
                    let idx: &[Value] = if n <= 4 { &small[..n] } else { &big };
                    cur = self.except_path(cur, idx, 0, sp, s0, s1, floc)?;
                }
                Ok(cur)
            }
            Node::ActionSub { boxed, act, sub } => {
                let a = self.eval(act, s0, s1)?.as_bool()?;
                // Java: Tool.eval OPCODE_aa / OPCODE_sa: `<A>_e` is false when A is and `[A]_e` is true when A is; `e` is not evaluated then
                if a == *boxed {
                    return Ok(Value::Bool(a));
                }
                let unchanged = {
                    let cur = self.eval(sub, s0, s1)?;
                    let empty = self.empty();
                    let nxt = self.eval(sub, s1, &empty)?;
                    cur.eq_val(&nxt)?
                };
                if *boxed {
                    Ok(Value::Bool(a || unchanged))
                } else {
                    Ok(Value::Bool(a && !unchanged))
                }
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
            Node::SubstIn(subs, body, cacheable, cache) => {
                let saved = self.substs.borrow().clone();
                if *cacheable {
                    let hit = match &*cache.borrow() {
                        Some((outer, res)) if outer.same(&saved) => Some(res.clone()),
                        _ => None,
                    };
                    if let Some(res) = hit {
                        *self.substs.borrow_mut() = res;
                        let r = self.eval(body, s0, s1);
                        *self.substs.borrow_mut() = saved;
                        return r;
                    }
                }
                for (decl, a) in subs {
                    let slot = match self.eval_arg(a, s0, s1) {
                        Ok(sl) => sl,
                        Err(e) => {
                            *self.substs.borrow_mut() = saved;
                            return Err(e);
                        }
                    };
                    let next = self.substs.borrow().push(SubstEntry { decl: *decl, slot });
                    *self.substs.borrow_mut() = next;
                }
                if *cacheable {
                    *cache.borrow_mut() = Some((saved.clone(), self.substs.borrow().clone()));
                }
                let r = self.eval(body, s0, s1);
                *self.substs.borrow_mut() = saved;
                r
            }
            Node::Temporal(_) => fail("Attempted to evaluate a temporal formula in a context where only state predicates are allowed."),
            Node::Unsupported(what) => not_ported(format!("tlc-rs: unsupported construct: {}", what)),
            Node::Fail(msg) => fail(msg.clone()),
            _ => unreachable!("eval_heavy: not a heavy node"),
        }
    }

    fn var_name(&self, i: u32) -> String {
        self.var_names.borrow().get(i as usize).map(|n| n.to_string()).unwrap_or_else(|| format!("#{}", i))
    }

    fn eval_bi(&self, b: B, es: &[Ex], s0: &[Value], s1: &[Value]) -> R<Value> {
        if b == B::Cdot {
            // Java: Tool.getNextStates / eval / enabled, OPCODE_cdot without `-Dtlc2.tool.impl.Tool.cdot=true`
            return fail("The current version of TLC does not support action composition.  An incomplete implementation can be enabled via the tlc2.tool.impl.Tool.cdot=true java property.");
        }
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
        // `x, y \in S` binds every variable to the element; `<<x, y>> \in S` destructures a tuple (no temporary vector)
        if !b.tuple {
            for i in 0..b.nvars {
                self.set_slot(b.slot + i, Slot::V(el.clone()));
            }
            return Ok(());
        }
        match el {
            Value::Tuple(t) if t.len() == b.nvars as usize => {
                for (i, x) in t.iter().enumerate() {
                    self.set_slot(b.slot + i as u32, Slot::V(x.clone()));
                }
                Ok(())
            }
            _ => fail(format!("Attempted to bind the tuple of {} variables to the value
{}", b.nvars, el.to_tla())),
        }
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

    /// Java: `ContextEnumerator`: all range sets are evaluated first (in order); the FIRST variable varies fastest.
    pub fn for_each_binding_cb(
        &self,
        bounds: &[BoundIr],
        i: usize,
        evals: &dyn Fn(&Ex) -> R<Value>,
        f: &mut dyn FnMut(&Ev) -> R<bool>,
    ) -> R<bool> {
        let bounds = &bounds[i..];
        if bounds.is_empty() {
            return f(self);
        }
        fn not_a_set(set: &Value) -> R<bool> {
            fail(format!(
                "Attempted to enumerate the elements of the non-set value
{}
in a quantifier or set constructor.",
                set.to_tla()
            ))
        }
        if bounds.len() == 1 {
            // elements are visited lazily (SUBSET S and {x \in S : P} are generated on demand: Java's enumerators)
            let b = &bounds[0];
            let set = evals(&b.set)?;
            if !set.is_set_like() {
                return not_a_set(&set);
            }
            return set.try_each(&mut |el| {
                self.bind_bound(b, el)?;
                f(self)
            });
        }
        // up to 4 ranges live on the stack (no heap traffic per quantifier evaluation)
        let n = bounds.len();
        let mut doms_a: [Value; 4] = [Value::Undef, Value::Undef, Value::Undef, Value::Undef];
        let mut doms_v: Vec<Value>;
        let doms: &mut [Value] = if n <= 4 {
            &mut doms_a[..n]
        } else {
            doms_v = vec![Value::Undef; n];
            &mut doms_v[..]
        };
        for (k, b) in bounds.iter().enumerate() {
            let set = evals(&b.set)?;
            if !set.is_set_like() {
                return not_a_set(&set);
            }
            doms[k] = set;
        }
        // materialize the elements of every range (empty range => no bindings)
        let mut lists_a: [Option<Rc<Vec<Value>>>; 4] = [None, None, None, None];
        let mut lists_v: Vec<Option<Rc<Vec<Value>>>>;
        let lists: &mut [Option<Rc<Vec<Value>>>] = if n <= 4 {
            &mut lists_a[..n]
        } else {
            lists_v = vec![None; n];
            &mut lists_v[..]
        };
        for (k, d) in doms.iter().enumerate() {
            let e = d.enumerate()?;
            if e.is_empty() {
                return Ok(true);
            }
            lists[k] = Some(e);
        }
        let mut idx_a = [0usize; 4];
        let mut idx_v: Vec<usize>;
        let idx: &mut [usize] = if n <= 4 {
            &mut idx_a[..n]
        } else {
            idx_v = vec![0usize; n];
            &mut idx_v[..]
        };
        loop {
            for j in 0..n {
                self.bind_bound(&bounds[j], &lists[j].as_ref().unwrap()[idx[j]])?;
            }
            if !f(self)? {
                return Ok(false);
            }
            // odometer: the first variable advances fastest
            let mut j = 0;
            loop {
                idx[j] += 1;
                if idx[j] < lists[j].as_ref().unwrap().len() {
                    break;
                }
                idx[j] = 0;
                j += 1;
                if j == n {
                    return Ok(true);
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    /// `[cur EXCEPT !idx[k]..idx[last] = sp.val]`.  For a tuple or a function in normal form the position of the argument is found
    /// once, with the search `apply` does (same errors), the element is borrowed on the way down, the copy is built without the
    /// replaced element, and a value nothing else refers to (the result of an earlier EXCEPT clause) is updated in place.  Any other
    /// value, and an argument outside the domain, take `except_path_general`.
    #[allow(clippy::too_many_arguments)]
    fn except_path(&self, mut cur: Value, idx: &[Value], k: usize, sp: &ExceptIr, s0: &[Value], s1: &[Value], floc: &str) -> R<Value> {
        let pos = match cur.except_pos(&idx[k])? {
            Some(p) => p,
            None => return self.except_path_general(&cur, idx, k, sp.at_slot, &sp.val, s0, s1, floc),
        };
        let nv = if k + 1 == idx.len() {
            if sp.at_used {
                self.set_slot(sp.at_slot, Slot::V(cur.elem_at(pos).clone()));
            }
            self.eval(&sp.val, s0, s1)?
        } else {
            let sub = cur.take_or_clone_at(pos);
            self.except_path(sub, idx, k + 1, sp, s0, s1, floc)?
        };
        Ok(cur.replace_at(pos, nv))
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(never)]
    fn except_path_general(&self, cur: &Value, idx: &[Value], k: usize, at_slot: u32, val: &Ex, s0: &[Value], s1: &[Value], floc: &str) -> R<Value> {
        let arg = &idx[k];
        let sub = match cur.apply(arg) {
            Ok(v) => Some(v),
            Err(e) => {
                // only a miss in the domain leaves the function unchanged; other errors (e.g. comparing differently-typed
                // model values while searching the domain) are raised
                let miss = e.msg.contains("which is not in the domain of the function") || e.msg.contains("which is out of domain");
                if miss {
                    None
                } else {
                    return Err(e);
                }
            }
        };
        // Java: `result.select(lhs)` is null when a step of the path leaves the domain: warn and leave the value unchanged
        if sub.is_none() {
            self.warnings.borrow_mut().push((
                crate::ec::TLC_EXCEPT_APPLIED_TO_UNKNOWN_FIELD,
                format!("The EXCEPT was applied to non-existing fields of the value at\n{}", floc),
            ));
            return Ok(cur.clone());
        }
        if k + 1 == idx.len() {
            // `@` is the current value at the path
            match &sub {
                Some(old) => self.set_slot(at_slot, Slot::V(old.clone())),
                None => self.set_slot(at_slot, Slot::Poison(Box::new(TlcErr { code: crate::ec::GENERAL, msg: "Attempted to evaluate @ for a function argument outside the domain.".into(), not_ported: false, trail: vec![], fp_exc: false, frames: vec![], vsrc: vec![], pass: false }))),
            }
            if sub.is_none() {
                // outside the domain: TLC leaves the function unchanged
                return Ok(cur.clone());
            }
            let nv = self.eval(val, s0, s1)?;
            cur.except1(arg, nv)
        } else {
            let inner = self.except_path_general(&sub.unwrap(), idx, k + 1, at_slot, val, s0, s1, floc)?;
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
