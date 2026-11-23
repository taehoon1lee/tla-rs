//! Compiles the semantic graph (`tla_sany::sem`) to the evaluator's tree (`ir`).
//!
//! * every definition gets a `CompiledDef` (compiled on demand, memoized by `OpDef.id`);
//! * LET definitions are inlined at their use sites (slots of the enclosing frame);
//! * constants given by the configuration are folded into `Const` nodes unless an INSTANCE may substitute them.

use crate::ir::*;
use crate::value::*;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use tla_sany::ast::Loc;
use tla_sany::intern;
use tla_sany::sem::{self, Arg as SArg, Callee, EKind, OpArg, B};

pub struct Compiler {
    pub defs: HashMap<usize, Rc<CompiledDef>>,
    /// state variable index by declaration id
    pub var_index: HashMap<usize, u32>,
    /// values given to constants by the configuration (declaration id -> value)
    pub const_values: HashMap<usize, Value>,
    /// constant operators given by the configuration (declaration id -> definition)
    pub const_ops: HashMap<usize, Rc<sem::OpDef>>,
    /// declarations that some INSTANCE substitutes
    pub substitutable: HashSet<usize>,
    /// definition overrides (`CONSTANT Foo <- Bar` for definitions): sem def id -> replacement
    pub overrides: HashMap<usize, Rc<sem::OpDef>>,
    /// definitions replaced by a constant value (`CONSTANT Foo = v` naming an operator)
    pub def_values: HashMap<usize, Value>,
    pub natives: fn(&str, &str) -> Option<NativeFn>,
    ctx: Vec<FrameCtx>,
    let_depth: u32,
    /// slot of the function being defined (recursive function definitions)
    pending_self_slot: Option<u32>,
    primed_memo: HashMap<(usize, usize), bool>,
    /// sorted record domains, shared by every record constructor with the same fields
    rcd_doms: HashMap<Vec<u32>, Rc<Vec<Value>>>,
    /// node address -> source info (action labels)
    pub node_info: HashMap<usize, NodeInfo>,
    /// module of the definition / top expression being compiled
    pub cur_module: sem::Name,
}

struct FrameCtx {
    locals: HashMap<usize, u32>,
    /// LET definitions in scope: def id -> definition
    lets: HashMap<usize, Rc<sem::OpDef>>,
    next_slot: u32,
    max_slot: Rc<Cell<usize>>,
    at_slots: Vec<u32>,
    /// recursive LET operators compiled as closures: def id -> slot holding the closure
    rec_lets: HashMap<usize, u32>,
    /// number of slot allocations / slot references so far: an expression compiled without any is closed w.r.t. the frame
    events: u64,
    /// nullary LET definitions whose value is memoized: def id -> memo slot
    let_memo: HashMap<usize, u32>,
}

impl FrameCtx {
    fn new() -> FrameCtx {
        FrameCtx { locals: HashMap::new(), lets: HashMap::new(), next_slot: 0, max_slot: Rc::new(Cell::new(0)), at_slots: vec![], rec_lets: HashMap::new(), events: 0, let_memo: HashMap::new() }
    }
    fn alloc(&mut self) -> u32 {
        self.events += 1;
        let s = self.next_slot;
        self.next_slot += 1;
        if self.next_slot as usize > self.max_slot.get() {
            self.max_slot.set(self.next_slot as usize);
        }
        s
    }
}

fn nm(s: &str) -> sem::Name {
    sem::Name::from(s)
}

impl Compiler {
    pub fn new(natives: fn(&str, &str) -> Option<NativeFn>) -> Compiler {
        Compiler {
            defs: HashMap::new(),
            var_index: HashMap::new(),
            const_values: HashMap::new(),
            const_ops: HashMap::new(),
            substitutable: HashSet::new(),
            overrides: HashMap::new(),
            def_values: HashMap::new(),
            natives,
            ctx: vec![],
            let_depth: 0,
            pending_self_slot: None,
            primed_memo: HashMap::new(),
            rcd_doms: HashMap::new(),
            node_info: HashMap::new(),
            cur_module: std::sync::Arc::from(""),
        }
    }

    // ------------------------------------------------------------------ definitions

    pub fn compile_def(&mut self, d: &Rc<sem::OpDef>) -> Rc<CompiledDef> {
        // overrides given in the configuration name the original definition; INSTANCE copies (`I!Op`) follow it
        let orig_id = d.original().id;
        let d = match self.overrides.get(&d.id).or_else(|| self.overrides.get(&orig_id)) {
            Some(o) => o.clone(),
            None => d.clone(),
        };
        if let Some(c) = self.defs.get(&d.id) {
            return c.clone();
        }
        let params = d.params.borrow().clone();
        let cd = Rc::new(CompiledDef {
            id: d.id,
            name: d.name.clone(),
            module: d.module.clone(),
            nparams: params.len(),
            op_params: params.iter().map(|p| p.arity > 0).collect(),
            nslots: Cell::new(params.len()),
            body: RefCell::new(None),
            native: Cell::new(None),
            fast: Cell::new(crate::natives::Fast::None),
            first_test: std::cell::OnceCell::new(),
            level: d.level.get(),
            loc: d.loc,
            cache: RefCell::new(None),
            is_fcn: d.is_fcn_def.get(),
            src: d.clone(),
            state_cache: RefCell::new(None),
            label_cache: std::cell::OnceCell::new(),
            label_base: std::cell::OnceCell::new(),
            memo_kind: Cell::new(0),
            memo: RefCell::new(std::collections::HashMap::new()),
            memo_n: Cell::new(0),
            memo_calls: Cell::new(0),
            memo_hits: Cell::new(0),
            memo_decls: RefCell::new(None),
            deps: std::cell::OnceCell::new(),
            dep_cache: RefCell::new(None),
        });
        self.defs.insert(d.id, cd.clone());
        if let Some(v) = self.def_values.get(&d.id).or_else(|| self.def_values.get(&orig_id)).cloned() {
            *cd.body.borrow_mut() = Some(Rc::new(Node::Const(v)));
            return cd;
        }
        // native implementation of a standard-module operator
        let orig = d.original();
        if let Some(f) = (self.natives)(&orig.module, &orig.name) {
            cd.native.set(Some(f));
            cd.fast.set(crate::natives::lookup_fast(&orig.module, &orig.name));
            return cd;
        }
        if let Some(body) = d.body() {
            let mut fc = FrameCtx::new();
            for p in params.iter() {
                let s = fc.alloc();
                fc.locals.insert(p.id, s);
            }
            self.ctx.push(fc);
            let saved = self.let_depth;
            let saved_module = std::mem::replace(&mut self.cur_module, d.original().module.clone());
            self.let_depth = 0;
            self.pending_self_slot = None;
            if d.is_recursive_fcn.get() {
                if let Some(fp) = d.fcn_param.borrow().clone() {
                    let s = self.fc().alloc();
                    self.fc().locals.insert(fp.id, s);
                    self.pending_self_slot = Some(s);
                }
            }
            let ex = self.expr(&body);
            // Java: the body of an instance copy is the substitution node of the `INSTANCE` statement: its location lies in the module
            // that holds the statement (the copy's module), not in the instantiated module
            if body.loc == d.loc && d.module != d.original().module {
                if let Some(i) = self.node_info.get_mut(&(Rc::as_ptr(&ex) as usize)) {
                    i.module = d.module.clone();
                }
            }
            self.cur_module = saved_module;
            self.let_depth = saved;
            let fc = self.ctx.pop().unwrap();
            cd.nslots.set(fc.max_slot.get().max(params.len()));
            *cd.body.borrow_mut() = Some(ex);
        }
        cd
    }

    /// compile a top-level expression into a standalone frame (invariants, Init, Next, constraints ...)
    pub fn compile_top(&mut self, e: &sem::Expr) -> (Ex, Rc<Cell<usize>>) {
        let fc = FrameCtx::new();
        let cell = fc.max_slot.clone();
        self.ctx.push(fc);
        let ex = self.expr(e);
        self.ctx.pop();
        (ex, cell)
    }

    /// compile a top-level expression whose free bound variables `params` live in the first slots of the frame
    /// (used by the liveness translation: a leaf of a temporal formula under bounded quantifiers)
    pub fn compile_top_bound(&mut self, e: &sem::Expr, params: &[Rc<sem::Param>]) -> (Ex, Rc<Cell<usize>>) {
        let (a, _, cell) = self.compile_top_bound2(e, None, params);
        (a, cell)
    }

    /// like `compile_top_bound` for two expressions sharing a frame (`ENABLED <<A>>_v`: the action and its subscript)
    pub fn compile_top_bound2(&mut self, a: &sem::Expr, b: Option<&sem::Expr>, params: &[Rc<sem::Param>]) -> (Ex, Option<Ex>, Rc<Cell<usize>>) {
        let mut fc = FrameCtx::new();
        let cell = fc.max_slot.clone();
        for p in params {
            let s = fc.alloc();
            fc.locals.insert(p.id, s);
        }
        self.ctx.push(fc);
        let ea = self.expr(a);
        let eb = b.map(|x| self.expr(x));
        self.ctx.pop();
        (ea, eb, cell)
    }

    // ------------------------------------------------------------------ helpers

    fn fc(&mut self) -> &mut FrameCtx {
        self.ctx.last_mut().expect("frame")
    }

    fn konst(&self, v: Value) -> Ex {
        Rc::new(Node::Const(v))
    }

    fn unsupported(&self, what: impl Into<String>) -> Ex {
        Rc::new(Node::Unsupported(what.into()))
    }

    fn decl_ref(&self, d: &Rc<sem::OpDecl>) -> Rc<DeclRef> {
        let vi = self.var_index.get(&d.id).copied().unwrap_or(u32::MAX);
        Rc::new(DeclRef { id: d.id, name: d.name.clone(), is_var: d.kind == sem::DeclKind::Variable, var_index: vi, arity: d.arity })
    }

    /// `\E x, y \in S` is `\E x \in S, y \in S`; `<<x, y>> \in S` stays one bound with a tuple pattern
    fn bounds_flat(&mut self, groups: &[sem::BoundGroup]) -> Vec<BoundIr> {
        let mut out = vec![];
        for g in groups {
            // the set is compiled before the variables are bound
            let set = self.expr(&g.set);
            if g.tuple {
                let first = self.fc().next_slot;
                for p in &g.params {
                    let s = self.fc().alloc();
                    self.fc().locals.insert(p.id, s);
                }
                out.push(BoundIr { slot: first, nvars: g.params.len() as u32, tuple: true, set });
            } else {
                for p in &g.params {
                    let s = self.fc().alloc();
                    self.fc().locals.insert(p.id, s);
                    out.push(BoundIr { slot: s, nvars: 1, tuple: false, set: set.clone() });
                }
            }
        }
        out
    }

    fn bound_vars(&mut self, bv: &sem::BoundVars, set: Ex) -> BoundIr {
        let first = self.fc().next_slot;
        for p in &bv.params {
            let s = self.fc().alloc();
            self.fc().locals.insert(p.id, s);
        }
        BoundIr { slot: first, nvars: bv.params.len() as u32, tuple: bv.tuple, set }
    }

    /// an expression argument; a call-by-name argument that never touches the frame needs no frame copy
    fn val_arg(c: Ex, by_name: bool, closed: bool) -> Arg {
        if by_name && closed {
            Arg::ValClosed(c)
        } else {
            Arg::Val(c, by_name)
        }
    }

    fn arg(&mut self, a: &SArg) -> Arg {
        match a {
            SArg::Expr(e) => {
                let ev0 = self.fc().events;
                let c = self.expr(e);
                let closed = self.fc().events == ev0;
                // a bare state variable stands for the variable itself (it may be assigned: `XInit(x)` with `XInit(v) == v = 0`)
                let by_name = e.level >= sem::Level::Action || matches!(&*c, Node::Var(_)) || matches!(&*c, Node::Decl(dr) if dr.is_var);
                Self::val_arg(c, by_name, closed)
            }
            SArg::Op(oa) => Arg::Op(self.opref(oa)),
        }
    }

    /// a LET-local `INSTANCE M` copy of an operator that has a native implementation (e.g. `LET IO == INSTANCE IOUtils IN
    /// IO!Serialize(..)`): it is called like the module-level one instead of being inlined
    fn is_native_copy(&self, d: &Rc<sem::OpDef>) -> bool {
        let o = d.original();
        !Rc::ptr_eq(&o, d) && (self.natives)(&o.module, &o.name).is_some()
    }

    fn opref(&mut self, oa: &OpArg) -> OpRef {
        match oa {
            OpArg::Builtin(b, _) => OpRef::Builtin(*b),
            OpArg::Lambda(d) => OpRef::Lambda(self.lambda(d)),
            OpArg::Callee(c, _) => match c {
                Callee::Def(d) => {
                    if self.fc().lets.contains_key(&d.id) && !self.is_native_copy(d) {
                        OpRef::Lambda(self.lambda(d))
                    } else {
                        OpRef::Def(self.compile_def(d))
                    }
                }
                Callee::Param(p) => match self.fc().locals.get(&p.id).copied() {
                    Some(s) => {
                        self.fc().events += 1;
                        OpRef::Local(s)
                    }
                    None => OpRef::Lambda(self.lambda_unsupported()),
                },
                Callee::Decl(d) => {
                    if let Some(def) = self.const_ops.get(&d.id).cloned() {
                        OpRef::Def(self.compile_def(&def))
                    } else {
                        OpRef::Decl(d.id)
                    }
                }
            },
        }
    }

    fn lambda_unsupported(&mut self) -> Rc<LambdaDef> {
        Rc::new(LambdaDef { nparams: 0, nslots: 0, body: self.unsupported("operator argument") })
    }

    /// compile an operator definition used as a closure (LAMBDA / LET definition passed as an argument):
    /// the body runs in a copy of the enclosing frame; its parameters get fresh slots.
    fn lambda(&mut self, d: &Rc<sem::OpDef>) -> Rc<LambdaDef> {
        let params = d.params.borrow().clone();
        let mut saved: Vec<(usize, Option<u32>)> = vec![];
        let mut pslots = vec![];
        for p in &params {
            let s = self.fc().alloc();
            saved.push((p.id, self.fc().locals.insert(p.id, s)));
            pslots.push(s);
        }
        let body = match d.body() {
            Some(b) => self.expr(&b),
            None => self.unsupported("operator without body"),
        };
        for (id, old) in saved {
            match old {
                Some(o) => {
                    self.fc().locals.insert(id, o);
                }
                None => {
                    self.fc().locals.remove(&id);
                }
            }
        }
        // slot numbers of the parameters are consecutive starting at pslots[0]
        let first = pslots.first().copied().unwrap_or(0);
        let _ = first;
        Rc::new(LambdaDef { nparams: params.len(), nslots: first as usize, body })
    }

    /// does `e` mention the parameter `p`?
    fn mentions_param(e: &sem::Expr, p: &Rc<sem::Param>) -> bool {
        match &e.kind {
            EKind::Apply(Callee::Param(q), args) => {
                if Rc::ptr_eq(q, p) {
                    return true;
                }
                for a in args {
                    if let SArg::Expr(x) = a {
                        if Self::mentions_param(x, p) {
                            return true;
                        }
                    }
                }
                false
            }
            _ => e.children().iter().any(|c| Self::mentions_param(c, p)),
        }
    }

    /// is some occurrence of parameter `p` primed (`p'`, `UNCHANGED p`, or passed to a primed parameter)?
    fn primes_param(&mut self, e: &sem::Expr, p: &Rc<sem::Param>, depth: u32) -> bool {
        if depth > 200 {
            return false;
        }
        match &e.kind {
            EKind::Bi(B::Prime, a) | EKind::Bi(B::Unchanged, a) => {
                if Self::mentions_param(&a[0], p) {
                    return true;
                }
            }
            EKind::Apply(Callee::Def(d2), args) => {
                for (j, a) in args.iter().enumerate() {
                    if let SArg::Expr(x) = a {
                        if Self::mentions_param(x, p) && self.param_primed(d2, j) {
                            return true;
                        }
                    }
                }
            }
            _ => {}
        }
        for c in e.children() {
            if self.primes_param(&c, p, depth + 1) {
                return true;
            }
        }
        false
    }

    /// is parameter `i` of `d` primed somewhere in the body of `d`?  (such arguments are passed by name)
    fn param_primed(&mut self, d: &Rc<sem::OpDef>, i: usize) -> bool {
        let key = (d.id, i);
        if let Some(&b) = self.primed_memo.get(&key) {
            return b;
        }
        self.primed_memo.insert(key, false);
        let params = d.params.borrow().clone();
        let r = match (params.get(i), d.body()) {
            (Some(p), Some(b)) => {
                let p = p.clone();
                self.primes_param(&b, &p, 0)
            }
            _ => false,
        };
        self.primed_memo.insert(key, r);
        r
    }

    fn args_for(&mut self, d: &Rc<sem::OpDef>, args: &[SArg]) -> Vec<Arg> {
        let mut out = Vec::with_capacity(args.len());
        for (i, a) in args.iter().enumerate() {
            out.push(match a {
                SArg::Expr(e) => {
                    let ev0 = self.fc().events;
                    let c = self.expr(e);
                    let closed = self.fc().events == ev0;
                    let by_name = e.level >= sem::Level::Action
                        || (e.level >= sem::Level::State && self.param_primed(d, i))
                        || matches!(&*c, Node::Var(_))
                        || matches!(&*c, Node::Decl(dr) if dr.is_var);
                    Self::val_arg(c, by_name, closed)
                }
                SArg::Op(oa) => Arg::Op(self.opref(oa)),
            });
        }
        out
    }

    fn args_of(&mut self, args: &[SArg]) -> Vec<Arg> {
        args.iter().map(|a| self.arg(a)).collect()
    }

    // ------------------------------------------------------------------ expressions

    /// can `e` be evaluated once and cached (closed, constant, pure)?
    fn foldable(e: &sem::Expr) -> bool {
        if e.level != sem::Level::Const {
            return false;
        }
        match &e.kind {
            EKind::Num(_) | EKind::Str(_) => true,
            EKind::SetEnum(v) | EKind::Tuple(v) => v.iter().all(Self::foldable),
            EKind::Bi(b, args) => !matches!(b, B::Prime | B::Unchanged | B::Enabled) && args.iter().all(Self::foldable),
            EKind::Apply(Callee::Def(d), args) => {
                let ok_def = matches!(&*d.module, "Naturals" | "Integers" | "Reals" | "Sequences" | "FiniteSets")
                    || (args.is_empty() && d.level.get() == sem::Level::Const && !d.in_let.get() && !matches!(&*d.module, "TLC" | "TLCExt") && !matches!(&*d.original().module, "TLC" | "TLCExt"));
                ok_def
                    && args.iter().all(|a| match a {
                        SArg::Expr(x) => Self::foldable(x),
                        SArg::Op(_) => false,
                    })
            }
            _ => false,
        }
    }

    pub fn expr(&mut self, e: &sem::Expr) -> Ex {
        let n = self.expr_raw(e);
        if !matches!(&*n, Node::Const(_) | Node::Local(_) | Node::Var(_) | Node::PrimedVar(..) | Node::Unsupported(_)) {
            let const_sub = match &e.kind {
                EKind::BQuant { forall: false, bounds, .. } => bounds.iter().all(|b| b.set.level == sem::Level::Const),
                EKind::Apply(Callee::Def(_), args) => args.iter().all(|a| match a {
                    SArg::Expr(x) => x.level == sem::Level::Const,
                    SArg::Op(_) => true,
                }),
                _ => false,
            };
            let synthetic = matches!(&e.kind, EKind::Apply(Callee::Def(d), a) if a.is_empty() && e.loc == d.loc);
            // Java: the location of a reference to an instance definition is the `INSTANCE` statement, in the module that holds it
            let module = match &e.kind {
                EKind::Apply(Callee::Def(d), a) if synthetic && a.is_empty() => d.module.clone(),
                EKind::SubstIn(subs, _) if !subs.is_empty() => subs[0].module.clone(),
                _ => self.cur_module.clone(),
            };
            self.node_info.entry(Rc::as_ptr(&n) as usize).or_insert(NodeInfo { loc: e.loc, module, const_sub, synthetic });
        }
        if Self::foldable(e) && !matches!(&*n, Node::Const(_) | Node::Fold(..) | Node::Unsupported(_) | Node::Fail(_)) {
            // only worth it for operations (a bare definition call is cached by the definition itself)
            if matches!(&e.kind, EKind::Bi(..) | EKind::SetEnum(_) | EKind::Tuple(_) | EKind::Apply(..)) {
                return Rc::new(Node::Fold(n, RefCell::new(None)));
            }
        }
        self.maybe_memo(n)
    }

    /// A pure set-building expression (`A \cup B`, `{f(x) : x \in S}`, `{x \in S : P}`, `S \X T`, ...) is remembered by the values
    /// it reads: inside a `\E r \in SUBSET S : r \subseteq (sent \cup {..})` loop the right-hand side is the same for every `r`.
    fn maybe_memo(&mut self, n: Ex) -> Ex {
        let candidate = match &*n {
            Node::Bi(b, _) => matches!(b, sem::B::Union | sem::B::Intersect | sem::B::SetMinus | sem::B::UnionAll | sem::B::Subset),
            Node::SetOfAll(..) | Node::SubsetOf { .. } | Node::Times(_) | Node::SetOfFcns(..) | Node::SetOfRcds(_) => true,
            _ => false,
        };
        if !candidate {
            return n;
        }
        match crate::deps::memo_spec(&n) {
            Some(spec) => Rc::new(Node::Memo(Rc::new(MemoNode {
                inner: n,
                v0: spec.v0,
                v1: spec.v1,
                slots: spec.slots,
                cache: RefCell::new(Vec::new()),
                calls: Cell::new(0),
                hits: Cell::new(0),
                off: Cell::new(false),
            }))),
            None => n,
        }
    }

    fn expr_raw(&mut self, e: &sem::Expr) -> Ex {
        let loc = e.loc;
        match &e.kind {
            EKind::Num(t) => match parse_num(t) {
                Some(i) => self.konst(Value::Int(i)),
                None => Rc::new(Node::Unsupported(format!("integer literal {} out of range", t))),
            },
            EKind::Dec(a, b) => Rc::new(Node::Unsupported(format!("decimal literal {}.{}", a, b))),
            EKind::Str(s) => self.konst(Value::Str(intern::intern(s))),
            EKind::At => match self.fc().at_slots.last().copied() {
                Some(s) => {
                    self.fc().events += 1;
                    Rc::new(Node::Local(s))
                }
                None => self.unsupported("@ outside EXCEPT"),
            },
            EKind::Unsupported(s) => self.unsupported(format!("selector {}", s)),
            EKind::Apply(c, args) => self.apply(c, args, loc),
            EKind::Bi(b, es) => self.builtin(*b, es, loc),
            EKind::Tuple(es) => {
                let v: Vec<Ex> = es.iter().map(|x| self.expr(x)).collect();
                self.maybe_const(Node::Tuple(v))
            }
            EKind::SetEnum(es) => {
                let v: Vec<Ex> = es.iter().map(|x| self.expr(x)).collect();
                self.maybe_const(Node::SetEnum(v))
            }
            EKind::FcnApply(f, a) => {
                let fe = self.expr(f);
                let ae = self.expr(a);
                Rc::new(Node::FcnApply(fe, ae))
            }
            EKind::Record(r, f) => {
                let re = self.expr(r);
                Rc::new(Node::Record(re, intern::intern(f)))
            }
            EKind::SubsetOf(bv, set, pred) => {
                let s = self.expr(set);
                let b = self.bound_vars(bv, s);
                let p = self.expr(pred);
                Rc::new(Node::SubsetOf { bound: b, pred: p, filter_slots: Rc::new(vec![]) })
            }
            EKind::SetOfAll(ex, groups) => {
                let bs: Vec<BoundIr> = self.bounds_flat(groups);
                let b = self.expr(ex);
                Rc::new(Node::SetOfAll(b, bs))
            }
            EKind::FcnCons(groups, body) => {
                let self_slot = self.pending_self_slot.take();
                let bs: Vec<BoundIr> = self.bounds_flat(groups);
                let b = self.expr(body);
                Rc::new(Node::FcnCons(bs, b, self_slot, std::cell::OnceCell::new()))
            }
            EKind::SetOfFcns(a, b) => {
                let ae = self.expr(a);
                let be = self.expr(b);
                Rc::new(Node::SetOfFcns(ae, be))
            }
            EKind::RcdCons(fields) => {
                let v: Vec<(u32, Ex)> = fields.iter().map(|(n, x)| (intern::intern(n), self.expr(x))).collect();
                let mut order: Vec<usize> = (0..v.len()).collect();
                order.sort_by_key(|&i| v[i].0);
                let mut pos = vec![0usize; v.len()];
                for (rank, &i) in order.iter().enumerate() {
                    pos[i] = rank;
                }
                let key: Vec<u32> = order.iter().map(|&i| v[i].0).collect();
                let dom = self.rcd_doms.entry(key.clone()).or_insert_with(|| Rc::new(key.iter().map(|&id| Value::Str(id)).collect())).clone();
                Rc::new(Node::RcdCons(v, dom, pos))
            }
            EKind::SetOfRcds(fields) => {
                let v: Vec<(u32, Ex)> = fields.iter().map(|(n, x)| (intern::intern(n), self.expr(x))).collect();
                Rc::new(Node::SetOfRcds(v))
            }
            EKind::Except(f, specs) => {
                let fe = self.expr(f);
                let mut out = vec![];
                for s in specs {
                    let mut path = vec![];
                    for c in &s.path {
                        match c {
                            sem::ExceptComp::Field(n) => path.push(PathIr::Field(intern::intern(n))),
                            sem::ExceptComp::Index(ix) => {
                                if ix.len() == 1 {
                                    path.push(PathIr::Index(self.expr(&ix[0])));
                                } else {
                                    let v: Vec<Ex> = ix.iter().map(|x| self.expr(x)).collect();
                                    path.push(PathIr::Index(Rc::new(Node::Tuple(v))));
                                }
                            }
                        }
                    }
                    let at = self.fc().alloc();
                    self.fc().at_slots.push(at);
                    let val = self.expr(&s.val);
                    self.fc().at_slots.pop();
                    out.push(ExceptIr { path, at_slot: at, val });
                }
                let floc = format!("line {}, col {} to line {}, col {} of module {}", f.loc.bl, f.loc.bc, f.loc.el, f.loc.ec, self.cur_module);
                Rc::new(Node::Except(fe, out, Rc::from(floc.as_str())))
            }
            EKind::ActionSub { boxed, act, sub } => {
                let a = self.expr(act);
                let s = self.expr(sub);
                Rc::new(Node::ActionSub { boxed: *boxed, act: a, sub: s })
            }
            EKind::Fair { .. } => Rc::new(Node::Temporal(sem::Level::Temporal)),
            EKind::If(c, t, f) => {
                let (c, t, f) = (self.expr(c), self.expr(t), self.expr(f));
                Rc::new(Node::If(c, t, f))
            }
            EKind::Case(arms, other) => {
                let a: Vec<(Ex, Ex)> = arms.iter().map(|(c, v)| (self.expr(c), self.expr(v))).collect();
                let o = other.as_ref().map(|x| self.expr(x));
                Rc::new(Node::Case(a, o))
            }
            EKind::LetIn(defs, body) => {
                // recursive operators with parameters cannot be inlined: they become closures stored in slots
                let mut recs: Vec<(u32, Rc<sem::OpDef>)> = vec![];
                for d in defs {
                    if d.in_recursive.get() && !d.params.borrow().is_empty() {
                        let s = self.fc().alloc();
                        self.fc().rec_lets.insert(d.id, s);
                        recs.push((s, d.clone()));
                    }
                }
                // nullary definitions without primes are evaluated at most once per scope (Java: LazyValue)
                let mut memo_slots: Vec<u32> = vec![];
                for d in defs {
                    if d.params.borrow().is_empty()
                        && !d.in_recursive.get()
                        && !d.is_recursive_fcn.get()
                        && d.level.get() <= sem::Level::State
                        && d.body().map_or(false, |b| !matches!(&b.kind, EKind::Num(_) | EKind::Str(_)))
                    {
                        let s = self.fc().alloc();
                        self.fc().let_memo.insert(d.id, s);
                        memo_slots.push(s);
                    }
                }
                for d in defs {
                    self.fc().lets.insert(d.id, d.clone());
                }
                let mut lams = vec![];
                for (s, d) in &recs {
                    let l = self.lambda(d);
                    lams.push((*s, l));
                }
                let b = self.expr(body);
                for d in defs {
                    self.fc().lets.remove(&d.id);
                    self.fc().rec_lets.remove(&d.id);
                    self.fc().let_memo.remove(&d.id);
                }
                let b = if lams.is_empty() { b } else { Rc::new(Node::LetRec(lams, b)) };
                if memo_slots.is_empty() {
                    b
                } else {
                    Rc::new(Node::LetScope(memo_slots, b))
                }
            }
            EKind::BQuant { forall, bounds, body } => {
                let bs: Vec<BoundIr> = self.bounds_flat(bounds);
                let b = self.expr(body);
                if *forall {
                    Rc::new(Node::Forall(bs, b))
                } else {
                    Rc::new(Node::Exists(bs, b))
                }
            }
            EKind::UQuant { .. } => Rc::new(Node::Fail("TLC attempted to evaluate an unbounded quantified expression.".into())),
            EKind::TQuant { .. } => Rc::new(Node::Temporal(sem::Level::Temporal)),
            EKind::Choose(bv, set, body) => match set {
                Some(s) => {
                    let se = self.expr(s);
                    let b = self.bound_vars(bv, se);
                    let be = self.expr(body);
                    Rc::new(Node::Choose(b, be))
                }
                None => Rc::new(Node::Fail("TLC attempted to evaluate an unbounded CHOOSE.\nMake sure that the expression is of form CHOOSE x \\in S: P(x).".into())),
            },
            EKind::Conj(es) => {
                let v: Vec<Ex> = es.iter().map(|x| self.expr(x)).collect();
                Rc::new(Node::And(v))
            }
            EKind::Disj(es) => {
                let v: Vec<Ex> = es.iter().map(|x| self.expr(x)).collect();
                Rc::new(Node::Or(v))
            }
            EKind::SubstIn(subs, body) => {
                let mut v = vec![];
                for s in subs.iter() {
                    // Java: the value of a substitution is located in the module that holds the `INSTANCE` statement
                    let saved_module = std::mem::replace(&mut self.cur_module, s.module.clone());
                    let a = match &s.value {
                        SArg::Expr(e) if e.level == sem::Level::State => {
                            let ev0 = self.fc().events;
                            let c = self.expr(e);
                            let closed = self.fc().events == ev0;
                            Arg::State(c, closed)
                        }
                        SArg::Expr(e) => {
                            let ev0 = self.fc().events;
                            let c = self.expr(e);
                            let closed = self.fc().events == ev0;
                            Self::val_arg(c, e.level >= sem::Level::State, closed)
                        }
                        other => self.arg(other),
                    };
                    self.cur_module = saved_module;
                    v.push((s.target.id, a));
                }
                let b = self.expr(body);
                let cacheable = v.iter().all(|(_, a)| matches!(a, Arg::State(_, true) | Arg::ValClosed(_)));
                Rc::new(Node::SubstIn(v, b, cacheable, RefCell::new(None)))
            }
            EKind::Label(_, _, inner) => self.expr(inner),
        }
    }

    /// constant-fold literal tuples / sets when every element is a constant
    fn maybe_const(&mut self, n: Node) -> Ex {
        match &n {
            Node::Tuple(v) if v.iter().all(|x| matches!(&**x, Node::Const(_))) => {
                let vals: Vec<Value> = v.iter().map(|x| if let Node::Const(c) = &**x { c.clone() } else { unreachable!() }).collect();
                self.konst(Value::tuple(vals))
            }
            Node::SetEnum(v) if v.iter().all(|x| matches!(&**x, Node::Const(_))) => {
                let vals: Vec<Value> = v.iter().map(|x| if let Node::Const(c) = &**x { c.clone() } else { unreachable!() }).collect();
                match Value::set_from(vals) {
                    Ok(s) => self.konst(s),
                    Err(_) => Rc::new(n),
                }
            }
            _ => Rc::new(n),
        }
    }

    fn builtin(&mut self, b: B, es: &[sem::Expr], _loc: Loc) -> Ex {
        match b {
            B::True => self.konst(Value::Bool(true)),
            B::False => self.konst(Value::Bool(false)),
            B::Boolean => self.konst(Value::Set(Rc::new(vec![Value::Bool(false), Value::Bool(true)]))),
            B::String_ => self.konst(Value::StringSet),
            B::Prime => {
                // x' for a state variable, general e' otherwise
                if let EKind::Apply(Callee::Decl(d), args) = &es[0].kind {
                    if args.is_empty() && d.kind == sem::DeclKind::Variable && !self.substitutable.contains(&d.id) {
                        if let Some(&i) = self.var_index.get(&d.id) {
                            return Rc::new(Node::PrimedVar(i, Some(Rc::new((es[0].loc, self.cur_module.clone())))));
                        }
                    }
                }
                let e = self.expr(&es[0]);
                Rc::new(Node::Prime(e))
            }
            B::Unchanged => {
                let e = self.expr(&es[0]);
                // Java: `processUnchanged(.., expr, ..)` is on the call stack with the operand: it needs a position even for a variable
                self.node_info.entry(Rc::as_ptr(&e) as usize).or_insert(NodeInfo { loc: es[0].loc, module: self.cur_module.clone(), const_sub: false, synthetic: false });
                Rc::new(Node::Unchanged(e))
            }
            B::Not => {
                let e = self.expr(&es[0]);
                Rc::new(Node::Not(e))
            }
            B::And => {
                let (a, c) = (self.expr(&es[0]), self.expr(&es[1]));
                Rc::new(Node::And(vec![a, c]))
            }
            B::Or => {
                let (a, c) = (self.expr(&es[0]), self.expr(&es[1]));
                Rc::new(Node::Or(vec![a, c]))
            }
            B::Implies => {
                let (a, c) = (self.expr(&es[0]), self.expr(&es[1]));
                Rc::new(Node::Implies(a, c))
            }
            B::Equiv => {
                let (a, c) = (self.expr(&es[0]), self.expr(&es[1]));
                Rc::new(Node::Equiv(a, c))
            }
            B::Eq => {
                let (a, c) = (self.expr(&es[0]), self.expr(&es[1]));
                Rc::new(Node::Eq(a, c))
            }
            B::Neq => {
                let (a, c) = (self.expr(&es[0]), self.expr(&es[1]));
                Rc::new(Node::Neq(a, c))
            }
            B::In => {
                let (a, c) = (self.expr(&es[0]), self.expr(&es[1]));
                Rc::new(Node::In(a, c))
            }
            B::NotIn => {
                let (a, c) = (self.expr(&es[0]), self.expr(&es[1]));
                Rc::new(Node::NotIn(a, c))
            }
            B::Times => {
                let v: Vec<Ex> = es.iter().map(|x| self.expr(x)).collect();
                Rc::new(Node::Times(v))
            }
            B::Always | B::Eventually | B::LeadsTo | B::TemporalImplies => Rc::new(Node::Temporal(sem::Level::Temporal)),
            B::Enabled | B::Cdot => {
                let v: Vec<Ex> = es.iter().map(|x| self.expr(x)).collect();
                Rc::new(Node::Bi(b, v))
            }
            _ => {
                let v: Vec<Ex> = es.iter().map(|x| self.expr(x)).collect();
                Rc::new(Node::Bi(b, v))
            }
        }
    }

    fn apply(&mut self, c: &Callee, args: &[SArg], loc: Loc) -> Ex {
        match c {
            Callee::Param(p) => {
                let slot = match self.fc().locals.get(&p.id).copied() {
                    Some(s) => s,
                    None => {
                        if args.is_empty() && p.arity == 0 {
                            if let Some(x) = crate::spec::inline_param(p.id) {
                                return self.expr(&x);
                            }
                        } else if let Some(od) = crate::spec::inline_op(p.id) {
                            return self.apply(&Callee::Def(od), args, loc);
                        }
                        return self.unsupported(format!("unbound parameter {}", p.name));
                    }
                };
                self.fc().events += 1;
                if args.is_empty() && p.arity == 0 {
                    Rc::new(Node::Local(slot))
                } else {
                    let a = self.args_of(args);
                    Rc::new(Node::CallLocal(slot, a))
                }
            }
            Callee::Decl(d) => {
                if args.is_empty() && d.arity == 0 {
                    if !self.substitutable.contains(&d.id) {
                        if let Some(def) = self.const_ops.get(&d.id).cloned() {
                            let cd = self.compile_def(&def);
                            return Rc::new(Node::Call(cd, vec![], loc));
                        }
                    }
                    if !self.substitutable.contains(&d.id) {
                        if d.kind == sem::DeclKind::Variable {
                            if let Some(&i) = self.var_index.get(&d.id) {
                                return Rc::new(Node::Var(i));
                            }
                        } else if let Some(v) = self.const_values.get(&d.id) {
                            return self.konst(v.clone());
                        }
                    }
                    Rc::new(Node::Decl(self.decl_ref(d)))
                } else {
                    // constant operator with arguments
                    if let Some(def) = self.const_ops.get(&d.id).cloned() {
                        let cd = self.compile_def(&def);
                        let a = self.args_for(&def, args);
                        return Rc::new(Node::Call(cd, a, loc));
                    }
                    let a = self.args_of(args);
                    Rc::new(Node::CallDecl(self.decl_ref(d), a))
                }
            }
            Callee::Def(d) => {
                if let Some(&slot) = self.fc().rec_lets.get(&d.id) {
                    self.fc().events += 1;
                    let a = self.args_of(args);
                    return Rc::new(Node::CallLocal(slot, a));
                }
                if self.fc().lets.contains_key(&d.id) && !self.is_native_copy(d) {
                    return self.inline_let(d, args);
                }
                let cd = self.compile_def(d);
                if let Some(nf) = cd.native.get() {
                    let orig = d.original();
                    if args.len() == 2 && matches!(&*orig.module, "Naturals" | "Integers") {
                        let op = match &*orig.name {
                            "+" => Some(ArithOp::Plus),
                            "-" => Some(ArithOp::Minus),
                            "*" => Some(ArithOp::Times),
                            "<" => Some(ArithOp::Lt),
                            ">" => Some(ArithOp::Gt),
                            r"\leq" => Some(ArithOp::Le),
                            r"\geq" => Some(ArithOp::Ge),
                            ".." => Some(ArithOp::DotDot),
                            _ => None,
                        };
                        if let (Some(op), SArg::Expr(x), SArg::Expr(y)) = (op, &args[0], &args[1]) {
                            let (a, b) = (self.expr(x), self.expr(y));
                            return Rc::new(Node::Arith(op, a, b, nf));
                        }
                    }
                }
                let a = self.args_for(d, args);
                Rc::new(Node::Call(cd, a, loc))
            }
        }
    }

    fn inline_let(&mut self, d: &Rc<sem::OpDef>, args: &[SArg]) -> Ex {
        if self.let_depth > 40 {
            return self.unsupported("deeply recursive LET operator");
        }
        let body = match d.body() {
            Some(b) => b,
            None => return self.unsupported("LET operator without body"),
        };
        let params = d.params.borrow().clone();
        if params.is_empty() {
            self.let_depth += 1;
            let saved_pending = self.pending_self_slot.take();
            let mut fp_saved: Option<(usize, Option<u32>)> = None;
            if d.is_recursive_fcn.get() {
                if let Some(fp) = d.fcn_param.borrow().clone() {
                    let s = self.fc().alloc();
                    fp_saved = Some((fp.id, self.fc().locals.insert(fp.id, s)));
                    self.pending_self_slot = Some(s);
                }
            }
            let b = self.expr(&body);
            if let Some((id, old)) = fp_saved {
                match old {
                    Some(o) => {
                        self.fc().locals.insert(id, o);
                    }
                    None => {
                        self.fc().locals.remove(&id);
                    }
                }
            }
            self.pending_self_slot = saved_pending;
            self.let_depth -= 1;
            if let Some(slot) = self.fc().let_memo.get(&d.id).copied() {
                return Rc::new(Node::LetUse(slot, b));
            }
            return b;
        }
        // fresh slots for the parameters at this call site
        let compiled_args = self.args_for(d, args);
        let mut saved: Vec<(usize, Option<u32>)> = vec![];
        let mut assigns = vec![];
        for (p, a) in params.iter().zip(compiled_args.into_iter()) {
            let s = self.fc().alloc();
            saved.push((p.id, self.fc().locals.insert(p.id, s)));
            assigns.push((s, a));
        }
        self.let_depth += 1;
        let b = self.expr(&body);
        self.let_depth -= 1;
        for (id, old) in saved {
            match old {
                Some(o) => {
                    self.fc().locals.insert(id, o);
                }
                None => {
                    self.fc().locals.remove(&id);
                }
            }
        }
        Rc::new(Node::InlineCall { assigns, body: b })
    }
}

/// decimal / `\b` `\o` `\h` literals
pub fn parse_num(t: &str) -> Option<i32> {
    let t = t.trim();
    if let Some(r) = t.strip_prefix("\\b").or_else(|| t.strip_prefix("\\B")) {
        return i64::from_str_radix(r, 2).ok().and_then(|x| i32::try_from(x).ok());
    }
    if let Some(r) = t.strip_prefix("\\o").or_else(|| t.strip_prefix("\\O")) {
        return i64::from_str_radix(r, 8).ok().and_then(|x| i32::try_from(x).ok());
    }
    if let Some(r) = t.strip_prefix("\\h").or_else(|| t.strip_prefix("\\H")) {
        return i64::from_str_radix(r, 16).ok().and_then(|x| i32::try_from(x).ok());
    }
    t.parse::<i64>().ok().and_then(|x| i32::try_from(x).ok())
}
