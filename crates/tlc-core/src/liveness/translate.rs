//! Port of `Liveness.astToLive` / `astToLiveAppl` (tlc2.tool.liveness.Liveness): translate a (temporal) formula of the
//! specification into a `Ln` tree.  Bounded quantifiers are expanded over their (constant) domains, operator calls whose
//! body is temporal are expanded, everything else becomes a state / action predicate (a "leaf").
//!
//! Java passes a `Context` (bound variable values, INSTANCE substitutions) down the recursion; here `bound` holds the
//! values of the enclosing bound variables and `wraps` the enclosing `SubstIn` / `LetIn` scopes, with which every leaf is
//! wrapped before it is compiled.

use super::ln::*;
use crate::ec;
use crate::eval::Ev;
use crate::spec::Setup;
use crate::value::*;
use std::rc::Rc;
use tla_sany::sem::{self, Arg, BoundGroup, Callee, EKind, Expr, Level, B};

pub enum TrErr {
    Eval(Box<TlcErr>),
    /// `TLC_LIVE_CANNOT_HANDLE_FORMULA` with the given text
    Handle(String),
    /// any other error of the liveness machinery (code, message)
    Code(i32, String),
    /// a formula shape this port cannot translate yet (Java handles it): liveness checking is skipped
    Unsupported(String),
}

impl From<Box<TlcErr>> for TrErr {
    fn from(e: Box<TlcErr>) -> TrErr {
        TrErr::Eval(e)
    }
}

type Res = Result<Ln, TrErr>;

enum Wrap {
    Subst(Rc<Vec<sem::Subst>>),
    Let(Vec<Rc<sem::OpDef>>),
}

pub struct Translator<'a> {
    pub setup: &'a mut Setup,
    ev: Rc<Ev>,
    bound: Vec<(Rc<sem::Param>, Value)>,
    wraps: Vec<Wrap>,
    depth: u32,
}

pub fn lv(l: Level) -> u8 {
    match l {
        Level::Const => LEVEL_CONST,
        Level::State => LEVEL_VAR,
        Level::Action => LEVEL_ACTION,
        Level::Temporal => LEVEL_TEMPORAL,
    }
}

pub fn loc_text(e: &Expr, module: &str) -> String {
    format!("line {}, col {} to line {}, col {} of module {}", e.loc.bl, e.loc.bc, e.loc.el, e.loc.ec, module)
}

impl<'a> Translator<'a> {
    pub fn new(setup: &'a mut Setup) -> Translator<'a> {
        let ev = setup.ev.clone();
        // the leaves are compiled outside of a definition: their source positions are in the root module
        if setup.comp.cur_module.is_empty() {
            setup.comp.cur_module = std::sync::Arc::from(&*setup.root.name);
        }
        Translator { setup, ev, bound: vec![], wraps: vec![], depth: 0 }
    }

    pub fn set_bound(&mut self, b: Vec<(Rc<sem::Param>, Value)>) {
        self.bound = b;
    }

    fn handle<T>(&self, e: &Expr) -> Result<T, TrErr> {
        Err(TrErr::Handle(loc_text(e, &self.setup.root.name)))
    }

    /// the expression wrapped in the enclosing `SubstIn` / `LetIn` scopes (outermost first)
    fn wrap_expr(&self, e: &Expr) -> Expr {
        let mut cur = e.clone();
        for w in self.wraps.iter().rev() {
            cur = match w {
                Wrap::Subst(s) => Expr::new(EKind::SubstIn(s.clone(), cur.clone()), cur.loc, cur.level),
                Wrap::Let(d) => Expr::new(EKind::LetIn(d.clone(), cur.clone()), cur.loc, cur.level),
            };
        }
        cur
    }

    fn params(&self) -> Vec<Rc<sem::Param>> {
        self.bound.iter().map(|(p, _)| p.clone()).collect()
    }

    fn values(&self) -> Vec<Value> {
        self.bound.iter().map(|(_, v)| v.clone()).collect()
    }

    fn make_leaf(&mut self, e: &Expr) -> Leaf {
        let ex = self.wrap_expr(e);
        let params = self.params();
        let (code, nslots) = self.setup.comp.compile_top_bound(&ex, &params);
        Leaf { ex: code, sub: None, nslots, bound: self.values(), text: loc_text(e, &self.setup.root.name) }
    }

    /// evaluate a constant-level expression in the current bound context
    pub fn eval_const(&mut self, e: &Expr) -> R<Value> {
        let leaf = self.make_leaf(e);
        let empty = self.ev.empty();
        leaf.eval_value(&self.ev, &empty, &empty)
    }

    /// `astToLive(tool, expr, con, level)`: a leaf of the given level
    fn leaf_of(&mut self, e: &Expr, level: u8) -> Res {
        if level == LEVEL_CONST {
            return match self.eval_const(e)? {
                Value::Bool(b) => Ok(Ln::bool_(b)),
                other => Err(TrErr::Eval(Box::new(TlcErr {
                    code: ec::TLC_EXPECTED_VALUE,
                    msg: format!("TLC expected a value of type boolean, but found {}", other.to_tla()),
                    not_ported: false,
                    trail: vec![],
                    fp_exc: false,
                }))),
            };
        }
        let leaf = self.make_leaf(e);
        if level == LEVEL_VAR {
            Ok(Ln::new(LnNode::State(Rc::new(StateLeaf { tag: Default::default(), leaf, enabled: false }))))
        } else {
            Ok(Ln::new(LnNode::Action(Rc::new(ActionLeaf { tag: Default::default(), leaf }))))
        }
    }

    /// the level of `e` once the parameters bound by name (see `appl`) are replaced by the arguments they stand for
    fn inline_level(e: &Expr, depth: u32) -> Level {
        if depth > 40 {
            return e.level;
        }
        if let EKind::Apply(Callee::Param(q), a) = &e.kind {
            if a.is_empty() {
                if let Some(x) = crate::spec::inline_param(q.id) {
                    return Level::max(e.level, Self::inline_level(&x, depth + 1));
                }
            }
        }
        // only a constant-level leaf can hide a parameter bound by name: the other levels are already right
        if e.level != Level::Const {
            return e.level;
        }
        let mut level = e.level;
        for c in e.children() {
            level = Level::max(level, Self::inline_level(&c, depth + 1));
        }
        level
    }

    fn default_leaf(&mut self, e: &Expr) -> Res {
        let level = lv(Self::inline_level(e, 0));
        if level > LEVEL_ACTION {
            return self.handle(e);
        }
        self.leaf_of(e, level)
    }

    /// `astToLive(tool, expr, con)`
    pub fn translate(&mut self, e: &Expr) -> Res {
        self.depth += 1;
        if self.depth > 300 {
            self.depth -= 1;
            return self.handle(e);
        }
        let r = self.translate0(e);
        self.depth -= 1;
        r
    }

    fn translate0(&mut self, e: &Expr) -> Res {
        match &e.kind {
            EKind::LetIn(defs, body) => {
                self.wraps.push(Wrap::Let(defs.clone()));
                let r = self.translate(body);
                self.wraps.pop();
                r
            }
            EKind::SubstIn(subs, body) => {
                self.wraps.push(Wrap::Subst(subs.clone()));
                let r = self.translate(body);
                self.wraps.pop();
                r
            }
            EKind::Label(_, _, body) => self.translate(body),
            // a parameter bound by name to the argument of an inlined operator (see `appl`): translate the argument
            EKind::Apply(Callee::Param(p), args) if args.is_empty() && crate::spec::inline_param(p.id).is_some() => {
                let x = crate::spec::inline_param(p.id).unwrap();
                self.translate(&x)
            }
            EKind::Apply(Callee::Param(p), args) if !args.is_empty() && crate::spec::inline_op(p.id).is_some() => {
                let od = crate::spec::inline_op(p.id).unwrap();
                // the level of the call is that of its arguments (an argument that is a parameter bound by name counts as
                // the expression it stands for)
                fn eff_level(x: &Expr) -> Level {
                    match &x.kind {
                        EKind::Apply(Callee::Param(q), a) if a.is_empty() => match crate::spec::inline_param(q.id) {
                            Some(y) => eff_level(&y),
                            None => x.level,
                        },
                        _ => x.level,
                    }
                }
                let mut level = e.level;
                for a in args {
                    if let Arg::Expr(x) = a {
                        level = Level::max(level, eff_level(x));
                    }
                }
                let call = Expr::new(EKind::Apply(Callee::Def(od), args.clone()), e.loc, level);
                self.translate(&call)
            }
            EKind::Apply(callee, args) => self.appl(e, callee, args),
            EKind::Bi(op, args) => self.bi(e, *op, args),
            EKind::Conj(items) => self.junct(e, items, true),
            EKind::Disj(items) => self.junct(e, items, false),
            EKind::BQuant { forall, bounds, body } => self.bquant(e, *forall, bounds, body),
            EKind::If(c, t, f) => self.ite(e, c, t, f),
            EKind::Fair { strong, sub, act } => self.fair(e, *strong, sub, act),
            _ => self.default_leaf(e),
        }
    }

    fn appl(&mut self, e: &Expr, callee: &Callee, args: &[Arg]) -> Res {
        if let Callee::Def(d) = callee {
            // a user-defined operator whose body is temporal is expanded in place; anything else is a leaf
            // (the level of a call of a RECURSIVE operator is not reliable: look at the definitions)
            let temporal = lv(e.level) > LEVEL_ACTION || (d.in_recursive.get() && self.mentions_temporal(e, &mut vec![], 0));
            if temporal {
                let params = d.params.borrow().clone();
                if params.len() != args.len() {
                    return self.handle(e);
                }
                let body = match d.body() {
                    Some(b) => b,
                    None => return self.handle(e),
                };
                let mut pushed = 0;
                let mut ok = true;
                for (p, a) in params.iter().zip(args.iter()) {
                    match a {
                        // a parameter of an enclosing inlined operator that is bound by name stays an expression
                        Arg::Expr(x) if matches!(&x.kind, EKind::Apply(Callee::Param(q), a) if a.is_empty() && crate::spec::inline_param(q.id).is_some()) => {
                            crate::spec::register_inline_param(p.id, x.clone())
                        }
                        Arg::Expr(x) if x.level == Level::Const => match self.eval_const(x) {
                            Ok(v) => {
                                self.bound.push((p.clone(), v));
                                pushed += 1;
                            }
                            Err(_) => {
                                ok = false;
                                break;
                            }
                        },
                        // an argument that is not constant is bound by name (call by name): the leaves of the body that use the
                        // parameter are compiled with the argument expression in its place (Java: `getOpContext` + LazyValue)
                        // (only state- and action-level arguments: a temporal argument keeps the previous handling)
                        Arg::Expr(x) if lv(x.level) <= LEVEL_ACTION => crate::spec::register_inline_param(p.id, x.clone()),
                        Arg::Op(sem::OpArg::Callee(Callee::Def(od), _)) => crate::spec::register_inline_op(p.id, od.clone()),
                        // an operator parameter passed on
                        Arg::Op(sem::OpArg::Callee(Callee::Param(q), _)) => match crate::spec::inline_op(q.id) {
                            Some(od) => crate::spec::register_inline_op(p.id, od),
                            None => {
                                ok = false;
                                break;
                            }
                        },
                        other => {
                            if std::env::var_os("TLCRS_LIVE_DEBUG").is_some() {
                                eprintln!("live: argument of {} not bound: {:?}", d.name, std::mem::discriminant(other));
                                if let Arg::Op(o) = other {
                                    eprintln!("live:   op arg: {}", match o { sem::OpArg::Callee(Callee::Param(_), _) => "Param", sem::OpArg::Callee(Callee::Def(_), _) => "Def", sem::OpArg::Callee(Callee::Decl(_), _) => "Decl", sem::OpArg::Lambda(_) => "Lambda", sem::OpArg::Builtin(..) => "Builtin" });
                                }
                            }
                            ok = false;
                            break;
                        }
                    }
                }
                let r = if ok { self.translate(&body) } else { Err(TrErr::Unsupported(loc_text(e, &self.setup.root.name))) };
                for _ in 0..pushed {
                    self.bound.pop();
                }
                return r;
            }
        }
        self.default_leaf(e)
    }

    /// does `e` (or the definitions it calls) contain a temporal operator?
    fn mentions_temporal(&self, e: &Expr, seen: &mut Vec<usize>, depth: u32) -> bool {
        if depth > 60 {
            return false;
        }
        match &e.kind {
            EKind::Bi(B::Always | B::Eventually | B::LeadsTo, _) | EKind::Fair { .. } | EKind::TQuant { .. } => true,
            EKind::Apply(Callee::Def(d), args) => {
                if args.iter().any(|a| matches!(a, Arg::Expr(x) if self.mentions_temporal(x, seen, depth + 1))) {
                    return true;
                }
                if seen.contains(&d.id) {
                    return false;
                }
                seen.push(d.id);
                d.body().map_or(false, |b| self.mentions_temporal(&b, seen, depth + 1))
            }
            _ => e.children().iter().any(|c| self.mentions_temporal(c, seen, depth + 1)),
        }
    }

    fn bi(&mut self, e: &Expr, op: B, args: &[Expr]) -> Res {
        match op {
            B::Not => {
                let a = self.translate(&args[0])?;
                if a.level() > LEVEL_ACTION {
                    return Ok(Ln::neg(a));
                }
                self.leaf_of(e, a.level())
            }
            B::Implies => {
                let l = self.translate(&args[0])?;
                let r = self.translate(&args[1])?;
                let level = l.level().max(r.level());
                if level > LEVEL_ACTION {
                    return Ok(Ln::disj2(Ln::neg(l), r));
                }
                self.leaf_of(e, level)
            }
            B::And | B::Or => self.junct(e, args, op == B::And),
            B::Always => Ok(Ln::all(self.translate(&args[0])?)),
            B::Eventually => Ok(Ln::even(self.translate(&args[0])?)),
            B::LeadsTo => {
                let l = self.translate(&args[0])?;
                let r = self.translate(&args[1])?;
                Ok(Ln::all(Ln::disj2(Ln::neg(l), Ln::even(r))))
            }
            _ => self.default_leaf(e),
        }
    }

    fn junct(&mut self, e: &Expr, items: &[Expr], conj: bool) -> Res {
        let mut kids = vec![];
        for x in items {
            kids.push(self.translate(x)?);
        }
        let res = if conj { Ln::conj_flat(kids) } else { Ln::disj_flat(kids) };
        let level = res.level();
        if level > LEVEL_ACTION {
            return Ok(res);
        }
        self.leaf_of(e, level)
    }

    /// all contexts of the bounded quantifier: the first variable varies fastest (Java: `ContextEnumerator`); when a set
    /// depends on an earlier variable the variables are nested in order of appearance
    pub fn contexts(&mut self, bounds: &[BoundGroup]) -> R<Vec<Vec<(Rc<sem::Param>, Value)>>> {
        // one slot per variable (a tuple pattern binds several variables at once)
        struct Slot<'b> {
            params: Vec<Rc<sem::Param>>,
            tuple: bool,
            set: &'b Expr,
        }
        let mut slots: Vec<Slot> = vec![];
        for g in bounds {
            if g.tuple {
                slots.push(Slot { params: g.params.clone(), tuple: true, set: &g.set });
            } else {
                for p in &g.params {
                    slots.push(Slot { params: vec![p.clone()], tuple: false, set: &g.set });
                }
            }
        }
        // independent sets: enumerate with the first variable fastest
        let mut sets: Vec<Rc<Vec<Value>>> = vec![];
        let mut independent = true;
        for sl in &slots {
            match self.eval_const(sl.set) {
                Ok(v) if v.is_set_like() => sets.push(v.enumerate()?),
                _ => {
                    independent = false;
                    break;
                }
            }
        }
        let bind = |sl: &Slot, el: &Value| -> R<Vec<(Rc<sem::Param>, Value)>> {
            if sl.tuple {
                match el {
                    Value::Tuple(t) if t.len() == sl.params.len() => Ok(sl.params.iter().cloned().zip(t.iter().cloned()).collect()),
                    _ => fail("A tuple pattern of a bounded quantifier does not match the element."),
                }
            } else {
                Ok(vec![(sl.params[0].clone(), el.clone())])
            }
        };
        let mut out = vec![];
        if independent {
            if sets.iter().any(|s| s.is_empty()) {
                return Ok(out);
            }
            let mut idx = vec![0usize; slots.len()];
            loop {
                let mut ctx = vec![];
                for (i, sl) in slots.iter().enumerate() {
                    ctx.extend(bind(sl, &sets[i][idx[i]])?);
                }
                out.push(ctx);
                // odometer: the first variable is the fastest
                let mut k = 0;
                loop {
                    if k == slots.len() {
                        return Ok(out);
                    }
                    idx[k] += 1;
                    if idx[k] < sets[k].len() {
                        break;
                    }
                    idx[k] = 0;
                    k += 1;
                }
            }
        }
        // dependent sets: nested loops, the first variable outermost
        fn rec(
            tr: &mut Translator,
            slots: &[Slot],
            si: usize,
            cur: &mut Vec<(Rc<sem::Param>, Value)>,
            out: &mut Vec<Vec<(Rc<sem::Param>, Value)>>,
            bind: &dyn Fn(&Slot, &Value) -> R<Vec<(Rc<sem::Param>, Value)>>,
        ) -> R<()> {
            if si == slots.len() {
                out.push(cur.clone());
                return Ok(());
            }
            let set = tr.eval_const(slots[si].set)?;
            if !set.is_set_like() {
                return fail("Attempted to enumerate a non-set value in a bounded quantifier of a temporal formula.");
            }
            for el in set.enumerate()?.iter() {
                let n0 = tr.bound.len();
                let c0 = cur.len();
                for (p, v) in bind(&slots[si], el)? {
                    tr.bound.push((p.clone(), v.clone()));
                    cur.push((p, v));
                }
                let r = rec(tr, slots, si + 1, cur, out, bind);
                tr.bound.truncate(n0);
                cur.truncate(c0);
                r?;
            }
            Ok(())
        }
        rec(self, &slots, 0, &mut vec![], &mut out, &bind)?;
        Ok(out)
    }

    fn bquant(&mut self, e: &Expr, forall: bool, bounds: &[BoundGroup], body: &Expr) -> Res {
        let attempt = (|| -> Res {
            let ctxs = self.contexts(bounds)?;
            let mut kids = vec![];
            for ctx in ctxs {
                let n0 = self.bound.len();
                self.bound.extend(ctx);
                let r = self.translate(body);
                self.bound.truncate(n0);
                kids.push(r?);
            }
            if kids.is_empty() {
                return Ok(Ln::bool_(forall));
            }
            let res = if forall { Ln::conj_flat(kids) } else { Ln::disj_flat(kids) };
            let level = res.level();
            if level > LEVEL_ACTION {
                return Ok(res);
            }
            self.leaf_of(e, level)
        })();
        match attempt {
            Ok(r) => Ok(r),
            Err(err) => {
                // Java: the exception is swallowed; a formula of at most action level is treated as a plain predicate
                if lv(e.level) > LEVEL_ACTION {
                    return match err {
                        TrErr::Handle(t) => Err(TrErr::Handle(t)),
                        TrErr::Code(c, m) => Err(TrErr::Code(c, m)),
                        TrErr::Unsupported(m) => Err(TrErr::Unsupported(m)),
                        // Java normalizes sets lazily: a set such as {1, "a"} is fine until it is compared
                        TrErr::Eval(ev) if ev.msg.contains("Attempted to compare") => Err(TrErr::Unsupported(ev.msg.clone())),
                        TrErr::Eval(_) => self.handle(e),
                    };
                }
                self.leaf_of(e, lv(e.level))
            }
        }
    }

    fn ite(&mut self, e: &Expr, c: &Expr, t: &Expr, f: &Expr) -> Res {
        // a constant guard selects its branch (needed to expand recursive temporal operators)
        if c.level == Level::Const {
            if let Ok(Value::Bool(b)) = self.eval_const(c) {
                return self.translate(if b { t } else { f });
            }
        }
        let guard = self.translate(c)?;
        let e1 = self.translate(t)?;
        let e2 = self.translate(f)?;
        let res = Ln::disj2(Ln::conj2(guard.clone(), e1), Ln::conj2(Ln::neg(guard), e2));
        let level = res.level();
        if level > LEVEL_ACTION {
            return Ok(res);
        }
        self.leaf_of(e, level)
    }

    fn fair(&mut self, e: &Expr, strong: bool, sub: &Expr, act: &Expr) -> Res {
        // ENABLED <<A>>_e
        let a = self.wrap_expr(act);
        let s = self.wrap_expr(sub);
        let params = self.params();
        let (ex, sx, nslots) = self.setup.comp.compile_top_bound2(&a, Some(&s), &params);
        let enabled_leaf = Leaf { ex, sub: sx, nslots, bound: self.values(), text: loc_text(act, &self.setup.root.name) };
        let en = Ln::neg(Ln::new(LnNode::State(Rc::new(StateLeaf { tag: Default::default(), leaf: enabled_leaf, enabled: true }))));
        // <<A>>_e
        let angle = Expr::new(EKind::ActionSub { boxed: false, act: act.clone(), sub: sub.clone() }, e.loc, Level::Action);
        let leaf = self.make_leaf(&angle);
        let action = Ln::new(LnNode::Action(Rc::new(ActionLeaf { tag: Default::default(), leaf })));
        if strong {
            // SF_e(A) = <>[]-ENABLED <<A>>_e  \/  []<><<A>>_e
            Ok(Ln::disj2(Ln::even(Ln::all(en)), Ln::all(Ln::even(action))))
        } else {
            // WF_e(A) = []<>(-ENABLED <<A>>_e \/ <<A>>_e)
            Ok(Ln::all(Ln::even(Ln::disj2(en, action))))
        }
    }
}
