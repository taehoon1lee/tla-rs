//! Second half of the semantic analyzer: operator/function definitions, RECURSIVE, INSTANCE, expressions, levels.

use crate::analyze::*;
use crate::ast::{self, DefBody, IdKind, LetItem, Loc, QBinds, Shape};
use crate::ops;
use crate::sem::*;
use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::rc::Rc;

pub(crate) fn new_def(
    name: Name,
    params: Vec<Rc<Param>>,
    body: Option<Expr>,
    local: bool,
    kind: DefKind,
    module: Name,
    loc: Loc,
) -> Rc<OpDef> {
    Rc::new(OpDef {
        id: fresh_id(),
        name,
        params: RefCell::new(params),
        body: RefCell::new(body),
        local: Cell::new(local),
        kind,
        module,
        source: RefCell::new(None),
        loc,
        level: Cell::new(Level::Const),
        weights: RefCell::new(vec![]),
        in_recursive: Cell::new(false),
        is_defined: Cell::new(true),
        let_level: Cell::new(0),
        is_fcn_def: Cell::new(false),
        is_recursive_fcn: Cell::new(false),
        fcn_param: RefCell::new(None),
        in_let: Cell::new(false),
        compound: RefCell::new(vec![]),
    })
}

fn new_param(name: Name, arity: usize, loc: Loc) -> Rc<Param> {
    Rc::new(Param { id: fresh_id(), name, arity, loc })
}

fn arg_level(a: &Arg) -> Level {
    match a {
        Arg::Expr(e) => e.level,
        Arg::Op(OpArg::Callee(Callee::Def(d), _)) => d.level.get(),
        Arg::Op(OpArg::Lambda(d)) => d.level.get(),
        Arg::Op(_) => Level::Const,
    }
}

/// parameters whose level flows into the level of `e` (Java: `levelParams`)
fn level_params(e: &Expr, out: &mut HashSet<usize>) {
    fn arg(a: &Arg, out: &mut HashSet<usize>) {
        match a {
            Arg::Expr(e) => level_params(e, out),
            Arg::Op(OpArg::Callee(Callee::Param(p), _)) => {
                out.insert(p.id);
            }
            Arg::Op(OpArg::Lambda(d)) => {
                if let Some(b) = d.body() {
                    level_params(&b, out);
                }
            }
            Arg::Op(_) => {}
        }
    }
    match &e.kind {
        EKind::Num(_) | EKind::Dec(..) | EKind::Str(_) | EKind::At | EKind::Unsupported(_) => {}
        EKind::Apply(c, args) => {
            match c {
                Callee::Param(p) => {
                    out.insert(p.id);
                    for a in args {
                        arg(a, out);
                    }
                }
                Callee::Def(d) => {
                    let w = d.weights.borrow();
                    for (i, a) in args.iter().enumerate() {
                        if w.get(i).copied().unwrap_or(true) {
                            arg(a, out);
                        } else if let Arg::Op(_) = a {
                            // operator arguments: conservatively flow
                        }
                    }
                }
                Callee::Decl(_) => {
                    for a in args {
                        arg(a, out);
                    }
                }
            }
        }
        EKind::Bi(b, args) => {
            let (_, _, w) = b.props();
            for (i, a) in args.iter().enumerate() {
                if w[i.min(1)] {
                    level_params(a, out);
                }
            }
        }
        EKind::Tuple(v) | EKind::SetEnum(v) | EKind::Conj(v) | EKind::Disj(v) => v.iter().for_each(|x| level_params(x, out)),
        EKind::FcnApply(a, b) | EKind::SetOfFcns(a, b) => {
            level_params(a, out);
            level_params(b, out);
        }
        EKind::Record(a, _) => level_params(a, out),
        EKind::SubsetOf(_, s, p) => {
            level_params(s, out);
            level_params(p, out);
        }
        EKind::SetOfAll(e, bs) => {
            level_params(e, out);
            bs.iter().for_each(|b| level_params(&b.set, out));
        }
        EKind::FcnCons(bs, e) => {
            bs.iter().for_each(|b| level_params(&b.set, out));
            level_params(e, out);
        }
        EKind::RcdCons(v) | EKind::SetOfRcds(v) => v.iter().for_each(|(_, x)| level_params(x, out)),
        EKind::Except(e, specs) => {
            level_params(e, out);
            for s in specs {
                for c in &s.path {
                    if let ExceptComp::Index(v) = c {
                        v.iter().for_each(|x| level_params(x, out));
                    }
                }
                level_params(&s.val, out);
            }
        }
        EKind::ActionSub { act, sub, .. } => {
            let _ = (act, sub); // weight 0
        }
        EKind::Fair { .. } => {}
        EKind::If(a, b, c) => {
            level_params(a, out);
            level_params(b, out);
            level_params(c, out);
        }
        EKind::Case(arms, o) => {
            for (a, b) in arms {
                level_params(a, out);
                level_params(b, out);
            }
            if let Some(o) = o {
                level_params(o, out);
            }
        }
        EKind::LetIn(defs, b) => {
            // parameters used by the bodies of the LET definitions also influence the level (SANY: LetInNode.levelCheck)
            for d in defs.iter() {
                if let Some(db) = d.body() {
                    level_params(&db, out);
                }
            }
            level_params(b, out)
        }
        EKind::BQuant { bounds, body, .. } => {
            bounds.iter().for_each(|b| level_params(&b.set, out));
            level_params(body, out);
        }
        EKind::UQuant { body, .. } | EKind::TQuant { body, .. } => level_params(body, out),
        EKind::Choose(_, s, b) => {
            if let Some(s) = s {
                level_params(s, out);
            }
            level_params(b, out);
        }
        EKind::SubstIn(subs, b) => {
            level_params(b, out);
            for s in subs.iter() {
                arg(&s.value, out);
            }
        }
        EKind::Label(_, _, e) => level_params(e, out),
    }
}

impl<'a> Analyzer<'a> {
    fn mk(&self, kind: EKind, loc: Loc, level: Level) -> Expr {
        Expr::new(kind, loc, level)
    }

    fn maxl(es: &[Expr]) -> Level {
        es.iter().fold(Level::Const, |a, e| Level::max(a, e.level))
    }

    pub(crate) fn same_originally(&self, a: &Sym, b: &Sym) -> bool {
        if let (Sym::Def(x), Sym::Def(y)) = (a, b) {
            let (sx, sy) = (x.original(), y.original());
            if !Rc::ptr_eq(&sx, &sy) {
                return false;
            }
            return match self.table.get(&*sx.module) {
                Some(m) => m.param_free.get() || m.decls.borrow().is_empty(),
                None => self.cur_name == sx.module && self.cur.as_ref().map_or(true, |m| m.decls.borrow().is_empty()),
            };
        }
        false
    }

    // ------------------------------------------------------------------ definitions

    fn make_params(&mut self, decls: &[ast::OpDecl]) -> Vec<Rc<Param>> {
        let mut v = Vec::new();
        for p in decls {
            let prm = new_param(p.name.clone(), p.arity, p.loc);
            self.add_symbol(p.name.clone(), Sym::Param(prm.clone()), p.loc);
            v.push(prm);
        }
        v
    }

    fn finish_def_levels(&self, def: &Rc<OpDef>) {
        let body = match def.body() {
            Some(b) => b,
            None => return,
        };
        def.level.set(body.level);
        let mut lp = HashSet::new();
        level_params(&body, &mut lp);
        let w: Vec<bool> = def.params.borrow().iter().map(|p| lp.contains(&p.id)).collect();
        *def.weights.borrow_mut() = w;
    }

    pub(crate) fn process_operator(
        &mut self,
        d: &ast::OpDef,
        node: &Rc<ModuleNode>,
        defs: Option<&mut Vec<Rc<OpDef>>>,
    ) -> Result<Rc<OpDef>, ()> {
        let body_ast = match &d.body {
            DefBody::Expr(e) => e,
            _ => return Err(()),
        };
        self.push_scope();
        let params = self.make_params(&d.params);
        // already declared (RECURSIVE) or defined?
        let mut recursive_def: Option<Rc<OpDef>> = None;
        match self.resolve(&d.name) {
            Some(Sym::Def(od)) if od.in_recursive.get() && !od.is_defined.get() => {
                if od.let_level.get() == self.let_level {
                    let ok = od.params.borrow().len() == params.len() && params.last().map_or(true, |p| p.arity == 0);
                    if !ok {
                        self.err(d.loc, format!("Definition of {} has different arity than its RECURSIVE declaration.", od.name));
                    }
                    *od.params.borrow_mut() = params.clone();
                    recursive_def = Some(od);
                } else {
                    self.err(d.loc, format!("Recursive operator {} defined at wrong LET/IN level.", d.name));
                }
            }
            Some(_) => {
                self.err(d.loc, format!("Operator {} already defined or declared.", d.name));
            }
            None => {}
        }
        let body = self.gen_expr(body_ast);
        self.pop_scope();
        let body = body?;
        let def = match recursive_def {
            Some(od) => {
                *od.params.borrow_mut() = params;
                *od.body.borrow_mut() = Some(body);
                od.is_defined.set(true);
                od.local.set(d.local);
                self.finish_def_levels(&od);
                od
            }
            None => {
                let def = new_def(d.name.clone(), params, Some(body), d.local, DefKind::User, self.cur_name.clone(), d.loc);
                def.let_level.set(self.let_level);
                def.in_let.set(self.let_level > 0);
                self.finish_def_levels(&def);
                self.add_symbol(d.name.clone(), Sym::Def(def.clone()), d.loc);
                def
            }
        };
        match defs {
            Some(v) => v.push(def.clone()),
            None => node.defs.borrow_mut().push(def.clone()),
        }
        Ok(def)
    }

    pub(crate) fn process_function(
        &mut self,
        d: &ast::OpDef,
        node: &Rc<ModuleNode>,
        defs: Option<&mut Vec<Rc<OpDef>>>,
    ) -> Result<Rc<OpDef>, ()> {
        let (bounds_ast, body_ast) = match &d.body {
            DefBody::Function(b, e) => (b, e),
            _ => return Err(()),
        };
        // recursive declaration?
        let mut recursive_def: Option<Rc<OpDef>> = None;
        match self.resolve(&d.name) {
            Some(Sym::Def(od)) if od.in_recursive.get() && !od.is_defined.get() && od.let_level.get() == self.let_level => {
                recursive_def = Some(od);
            }
            Some(_) => {
                self.err(d.loc, format!("Operator {} already defined or declared.", d.name));
            }
            None => {}
        }
        self.push_scope();
        let fparam = new_param(d.name.clone(), 0, d.name_loc);
        if recursive_def.is_none() {
            self.add_symbol(d.name.clone(), Sym::Param(fparam.clone()), d.name_loc);
        }
        let flag = Rc::new(Cell::new(false));
        self.cur_fcn.push((fparam.clone(), flag.clone()));
        let r = (|| -> R<Expr> {
            let groups = self.gen_bound_groups(bounds_ast)?;
            let body = self.gen_expr(body_ast)?;
            let lvl = Level::max(Self::maxl(&groups.iter().map(|g| g.set.clone()).collect::<Vec<_>>()), body.level);
            Ok(self.mk(EKind::FcnCons(groups, body), d.loc, lvl))
        })();
        self.cur_fcn.pop();
        self.pop_scope();
        let body = r?;
        let def = match recursive_def {
            Some(od) => {
                *od.body.borrow_mut() = Some(body);
                od.is_defined.set(true);
                od
            }
            None => {
                let def = new_def(d.name.clone(), vec![], Some(body), d.local, DefKind::User, self.cur_name.clone(), d.loc);
                def.let_level.set(self.let_level);
                def.in_let.set(self.let_level > 0);
                self.add_symbol(d.name.clone(), Sym::Def(def.clone()), d.loc);
                def
            }
        };
        def.is_fcn_def.set(true);
        def.is_recursive_fcn.set(flag.get() || def.in_recursive.get());
        *def.fcn_param.borrow_mut() = if def.in_recursive.get() { None } else { Some(fparam) };
        self.finish_def_levels(&def);
        match defs {
            Some(v) => v.push(def.clone()),
            None => node.defs.borrow_mut().push(def.clone()),
        }
        Ok(def)
    }

    pub(crate) fn process_recursive(&mut self, decls: &[ast::OpDecl]) {
        for d in decls {
            let params: Vec<Rc<Param>> = (0..d.arity).map(|i| new_param(nm(&format!("_{}", i)), 0, d.loc)).collect();
            let def = new_def(d.name.clone(), params, None, false, DefKind::User, self.cur_name.clone(), d.loc);
            def.in_recursive.set(true);
            def.is_defined.set(false);
            def.let_level.set(self.let_level);
            def.in_let.set(self.let_level > 0);
            if self.add_symbol(d.name.clone(), Sym::Def(def.clone()), d.loc) {
                self.pending_rec.push(def);
            }
        }
    }

    // ------------------------------------------------------------------ INSTANCE

    /// builds the substitution list for `INSTANCE m WITH subs`
    fn process_subst(&mut self, subs: &[ast::Subst], instancee: &Rc<ModuleNode>, loc: Loc) -> R<Vec<Subst>> {
        let mut out: Vec<Subst> = Vec::new();
        let mut seen: HashSet<usize> = HashSet::new();
        for s in subs {
            let target = instancee.decls.borrow().iter().find(|d| d.name == s.name).cloned();
            let target = match target {
                Some(t) => t,
                None => {
                    self.err(
                        s.name_loc,
                        format!("Substitution for symbol {}, which is not a declared constant or variable of module {}.", s.name, instancee.name),
                    );
                    continue;
                }
            };
            if !seen.insert(target.id) {
                self.err(s.name_loc, format!("Multiple substitutions for symbol {}.", s.name));
                continue;
            }
            let val = if target.arity > 0 {
                self.gen_op_arg(&s.expr, target.arity, &s.name, 1)
            } else {
                self.gen_expr(&s.expr).map(Arg::Expr)
            };
            match val {
                Ok(v) => out.push(Subst { target, value: v, module: self.cur_name.clone() }),
                Err(()) => {}
            }
        }
        // implicit substitutions
        let decls: Vec<Rc<OpDecl>> = instancee.decls.borrow().clone();
        for d in decls {
            if seen.contains(&d.id) {
                continue;
            }
            match self.resolve(&d.name) {
                Some(sym) => {
                    let arg = match sym {
                        Sym::Decl(x) => {
                            if d.arity > 0 {
                                Arg::Op(OpArg::Callee(Callee::Decl(x), loc))
                            } else {
                                let lv = if x.kind == DeclKind::Variable { Level::State } else { Level::Const };
                                Arg::Expr(self.mk(EKind::Apply(Callee::Decl(x), vec![]), loc, lv))
                            }
                        }
                        Sym::Def(x) => {
                            if d.arity > 0 {
                                Arg::Op(OpArg::Callee(Callee::Def(x), loc))
                            } else {
                                let lv = x.level.get();
                                Arg::Expr(self.mk(EKind::Apply(Callee::Def(x), vec![]), loc, lv))
                            }
                        }
                        Sym::Param(x) => {
                            if d.arity > 0 {
                                Arg::Op(OpArg::Callee(Callee::Param(x), loc))
                            } else {
                                Arg::Expr(self.mk(EKind::Apply(Callee::Param(x), vec![]), loc, Level::Const))
                            }
                        }
                        Sym::Builtin(b) => {
                            if d.arity > 0 {
                                Arg::Op(OpArg::Builtin(b, loc))
                            } else {
                                Arg::Expr(self.mk(EKind::Bi(b, vec![]), loc, Level::Const))
                            }
                        }
                        Sym::Module(_) => {
                            self.err(loc, format!("Module name used where symbol {} is required.", d.name));
                            return Err(());
                        }
                    };
                    out.push(Subst { target: d, value: arg, module: self.cur_name.clone() });
                }
                None => {
                    self.err(
                        loc,
                        format!("Parameter {} of module {} needs to be instantiated.", d.name, instancee.name),
                    );
                }
            }
        }
        Ok(out)
    }

    fn subst_level(subs: &[Subst]) -> Level {
        subs.iter().fold(Level::Const, |a, s| Level::max(a, arg_level(&s.value)))
    }

    fn wrap_subst_in(&self, subs: &Rc<Vec<Subst>>, body: &Expr, loc: Loc) -> Expr {
        let lv = Level::max(body.level, Self::subst_level(subs));
        self.mk(EKind::SubstIn(subs.clone(), body.clone()), loc, lv)
    }

    pub(crate) fn generate_instance(&mut self, local: bool, inst: &ast::Instantiation, node: &Rc<ModuleNode>, loc: Loc, top: bool) -> R<()> {
        let instancee = match self.resolve_module(&inst.module) {
            Some(m) => m,
            None => {
                self.err(inst.module_loc, format!("Could not find module {}", inst.module));
                return Err(());
            }
        };
        let subs = Rc::new(self.process_subst(&inst.subs, &instancee, loc)?);
        let items: Vec<(Name, Sym, Loc)> = instancee.ctx.borrow().items.clone();
        for (_n, sym, _l) in items {
            let odn = match sym {
                Sym::Def(d) => d,
                _ => continue,
            };
            if odn.local.get() || odn.kind == DefKind::ModuleInstance {
                continue;
            }
            let new_odn: Rc<OpDef>;
            let odn_module_param_free = self.table.get(&*odn.module).map_or(true, |m| m.param_free.get());
            if !instancee.param_free.get() {
                if odn_module_param_free {
                    if local && top {
                        new_odn = self.copy_def(&odn, odn.name.clone(), None, true, loc, None);
                    } else {
                        new_odn = odn.clone();
                        self.add_symbol(odn.name.clone(), Sym::Def(odn.clone()), loc);
                    }
                } else {
                    let body = odn.body().map(|b| self.wrap_subst_in(&subs, &b, loc));
                    new_odn = self.copy_def(&odn, odn.name.clone(), body, local, loc, Some(&subs));
                    self.add_symbol(odn.name.clone(), Sym::Def(new_odn.clone()), loc);
                }
            } else if local {
                new_odn = self.copy_def(&odn, odn.name.clone(), None, true, loc, None);
                self.add_symbol(odn.name.clone(), Sym::Def(new_odn.clone()), loc);
            } else {
                new_odn = odn.clone();
                self.add_symbol(odn.name.clone(), Sym::Def(odn.clone()), loc);
            }
            if !Rc::ptr_eq(&new_odn, &odn) || true {
                let already = node.defs.borrow().iter().any(|d| Rc::ptr_eq(d, &new_odn));
                if !already {
                    node.defs.borrow_mut().push(new_odn);
                }
            }
        }
        let n = Rc::new(InstanceNode { name: None, local, module: instancee, subs: (*subs).clone(), params: vec![], loc });
        if top {
            node.instances.borrow_mut().push(n);
        }
        Ok(())
    }

    /// a new definition copying `odn` (shares params), with a new name/body
    fn copy_def(
        &mut self,
        odn: &Rc<OpDef>,
        name: Name,
        body: Option<Expr>,
        local: bool,
        loc: Loc,
        subs: Option<&Rc<Vec<Subst>>>,
    ) -> Rc<OpDef> {
        let params = odn.params.borrow().clone();
        let b = body.or_else(|| odn.body());
        let d = new_def(name, params, b, local, DefKind::User, self.cur_name.clone(), loc);
        *d.source.borrow_mut() = Some(odn.original());
        d.level.set(match (&*d.body.borrow(), subs) {
            (Some(b), _) => b.level,
            _ => odn.level.get(),
        });
        *d.weights.borrow_mut() = odn.weights.borrow().clone();
        d.is_fcn_def.set(odn.is_fcn_def.get());
        d.is_recursive_fcn.set(odn.is_recursive_fcn.get());
        *d.fcn_param.borrow_mut() = odn.fcn_param.borrow().clone();
        d
    }

    pub(crate) fn process_module_definition(
        &mut self,
        d: &ast::OpDef,
        inst: &ast::Instantiation,
        node: &Rc<ModuleNode>,
        defs: Option<&mut Vec<Rc<OpDef>>>,
    ) -> R<Rc<OpDef>> {
        let name = d.name.clone();
        self.push_scope();
        let args = self.make_params(&d.params);
        let instancee = match self.resolve_module(&inst.module) {
            Some(m) => m,
            None => {
                self.pop_scope();
                self.err(inst.module_loc, format!("Module name {} is not known in current context.", inst.module));
                return Err(());
            }
        };
        let subs = self.process_subst(&inst.subs, &instancee, d.loc);
        self.pop_scope();
        let subs = Rc::new(subs?);
        let items: Vec<(Name, Sym, Loc)> = instancee.ctx.borrow().items.clone();
        let mut new_defs: Vec<Rc<OpDef>> = Vec::new();
        for (_n, sym, _l) in items {
            let odn = match sym {
                Sym::Def(x) => x,
                _ => continue,
            };
            if odn.local.get() {
                continue;
            }
            let qn: Name = nm(&format!("{}!{}", name, odn.name));
            let mut params: Vec<Rc<Param>> = args.clone();
            params.extend(odn.params.borrow().iter().cloned());
            let new_odn = if odn.kind == DefKind::User || odn.kind == DefKind::Theorem {
                let body = odn.body().map(|b| if subs.is_empty() { b } else { self.wrap_subst_in(&subs, &b, d.loc) });
                let nd = new_def(qn.clone(), params, body, d.local, odn.kind, self.cur_name.clone(), d.loc);
                *nd.source.borrow_mut() = Some(odn.original());
                let mut comp = vec![name.clone()];
                comp.extend(odn.compound.borrow().iter().cloned());
                if odn.compound.borrow().is_empty() {
                    comp.push(odn.name.clone());
                }
                *nd.compound.borrow_mut() = comp;
                nd.level.set(nd.body().map(|b| b.level).unwrap_or(odn.level.get()));
                let mut w: Vec<bool> = args.iter().map(|_| true).collect();
                w.extend(odn.weights.borrow().iter().cloned());
                *nd.weights.borrow_mut() = w;
                nd.is_fcn_def.set(odn.is_fcn_def.get());
                nd.is_recursive_fcn.set(odn.is_recursive_fcn.get());
                *nd.fcn_param.borrow_mut() = odn.fcn_param.borrow().clone();
                nd
            } else {
                let nd = new_def(qn.clone(), params, None, d.local, DefKind::ModuleInstance, self.cur_name.clone(), d.loc);
                *nd.source.borrow_mut() = Some(odn.original());
                nd
            };
            self.add_symbol(qn, Sym::Def(new_odn.clone()), d.loc);
            new_defs.push(new_odn);
        }
        let module_def = new_def(name.clone(), args.clone(), None, d.local, DefKind::ModuleInstance, self.cur_name.clone(), d.loc);
        self.add_symbol(name.clone(), Sym::Def(module_def.clone()), d.name_loc);
        let inn = Rc::new(InstanceNode {
            name: Some(name),
            local: d.local,
            module: instancee,
            subs: (*subs).clone(),
            params: args,
            loc: d.loc,
        });
        match defs {
            Some(v) => {
                v.extend(new_defs);
                v.push(module_def.clone());
            }
            None => {
                node.defs.borrow_mut().extend(new_defs);
                node.instances.borrow_mut().push(inn);
            }
        }
        Ok(module_def)
    }

    // ------------------------------------------------------------------ bounds

    pub(crate) fn gen_bound_groups(&mut self, bounds: &[ast::Bound]) -> R<Vec<BoundGroup>> {
        // the sets are evaluated in the scope outside the new variables
        let mut sets = Vec::new();
        for b in bounds {
            sets.push(self.gen_expr(&b.set)?);
        }
        let mut out = Vec::new();
        for (b, set) in bounds.iter().zip(sets) {
            let mut params = Vec::new();
            for v in &b.vars {
                let p = new_param(v.name.clone(), 0, v.loc);
                self.add_symbol(v.name.clone(), Sym::Param(p.clone()), v.loc);
                params.push(p);
            }
            out.push(BoundGroup { params, tuple: b.tuple, set });
        }
        Ok(out)
    }

    fn bound_vars(&mut self, v: &ast::BoundVar) -> BoundVars {
        match v {
            ast::BoundVar::One(id) => {
                let p = new_param(id.name.clone(), 0, id.loc);
                self.add_symbol(id.name.clone(), Sym::Param(p.clone()), id.loc);
                BoundVars { params: vec![p], tuple: false }
            }
            ast::BoundVar::Tuple(ids, _) => {
                let mut ps = vec![];
                for id in ids {
                    let p = new_param(id.name.clone(), 0, id.loc);
                    self.add_symbol(id.name.clone(), Sym::Param(p.clone()), id.loc);
                    ps.push(p);
                }
                BoundVars { params: ps, tuple: true }
            }
        }
    }

    // ------------------------------------------------------------------ expressions

    fn num_lit(&self, text: &str) -> Name {
        nm(text)
    }

    fn arity_error(&mut self, loc: Loc, name: &str, expected: usize) {
        self.err(loc, format!("The operator {} requires {} arguments.", name, expected));
    }

    /// operator argument (Java `generateOpArg`): `expected` is the arity of the parameter being filled
    pub(crate) fn gen_op_arg(&mut self, a: &ast::Expr, expected: usize, op_name: &str, pos: usize) -> R<Arg> {
        let bad = |s: &mut Self| {
            s.err(a.loc, format!("Argument number {} to operator '{}' should be a {}-parameter operator.", pos, op_name, expected));
        };
        match &*a.kind {
            ast::ExprKind::Lambda(params, body) => {
                if params.len() != expected {
                    bad(self);
                    return Err(());
                }
                self.push_scope();
                let mut ps = vec![];
                for p in params {
                    let prm = new_param(p.name.clone(), 0, p.loc);
                    self.add_symbol(p.name.clone(), Sym::Param(prm.clone()), p.loc);
                    ps.push(prm);
                }
                let b = self.gen_expr(body);
                self.pop_scope();
                let b = b?;
                let d = new_def(nm("LAMBDA"), ps, Some(b), false, DefKind::User, self.cur_name.clone(), a.loc);
                self.finish_def_levels(&d);
                Ok(Arg::Op(OpArg::Lambda(d)))
            }
            ast::ExprKind::Id(g) => {
                let compound = Self::compound_name(g);
                let sym = self.resolve(&compound);
                match sym {
                    None => {
                        if !g.prefix.is_empty() && self.any_prefix_resolves(g) {
                            return Ok(Arg::Expr(self.mk(EKind::Unsupported(nm(&compound)), a.loc, Level::Const)));
                        }
                        self.err(a.loc, format!("Unknown operator: `{}'.", compound));
                        Err(())
                    }
                    Some(s) => {
                        let ar = sym_arity(&s);
                        if ar != expected {
                            bad(self);
                            return Err(());
                        }
                        match s {
                            Sym::Def(d) => Ok(Arg::Op(OpArg::Callee(Callee::Def(d), a.loc))),
                            Sym::Decl(d) => Ok(Arg::Op(OpArg::Callee(Callee::Decl(d), a.loc))),
                            Sym::Param(p) => Ok(Arg::Op(OpArg::Callee(Callee::Param(p), a.loc))),
                            Sym::Builtin(b) => Ok(Arg::Op(OpArg::Builtin(b, a.loc))),
                            Sym::Module(_) => {
                                bad(self);
                                Err(())
                            }
                        }
                    }
                }
            }
            _ => {
                bad(self);
                Err(())
            }
        }
    }

    fn compound_name(g: &ast::GenId) -> String {
        let mut s = String::new();
        for p in &g.prefix {
            s.push_str(&p.name);
            s.push('!');
        }
        s.push_str(&g.name);
        s
    }

    fn gen_args_for(&mut self, callee: &Sym, name: &str, args: &[&ast::Expr], loc: Loc) -> R<Vec<Arg>> {
        let mut out = Vec::new();
        // parameter arities of the callee
        let param_arities: Vec<usize> = match callee {
            Sym::Def(d) => d.params.borrow().iter().map(|p| p.arity).collect(),
            Sym::Decl(d) => vec![0; d.arity],
            Sym::Param(p) => vec![0; p.arity],
            _ => vec![],
        };
        let expected = sym_arity(callee);
        if args.len() != expected {
            self.arity_error(loc, name, expected);
            return Err(());
        }
        let mut failed = false;
        for (i, a) in args.iter().enumerate() {
            let ar = param_arities.get(i).copied().unwrap_or(0);
            let r = if ar == 0 { self.gen_expr(a).map(Arg::Expr) } else { self.gen_op_arg(a, ar, name, i + 1) };
            match r {
                Ok(x) => out.push(x),
                Err(()) => failed = true,
            }
        }
        if failed {
            Err(())
        } else {
            Ok(out)
        }
    }

    fn apply_level(&self, c: &Callee, args: &[Arg]) -> Level {
        match c {
            Callee::Def(d) => {
                let w = d.weights.borrow();
                let mut l = d.level.get();
                for (i, a) in args.iter().enumerate() {
                    if w.get(i).copied().unwrap_or(true) {
                        l = Level::max(l, arg_level(a));
                    }
                }
                l
            }
            Callee::Decl(d) => {
                let mut l = if d.kind == DeclKind::Variable { Level::State } else { Level::Const };
                for a in args {
                    l = Level::max(l, arg_level(a));
                }
                l
            }
            Callee::Param(_) => args.iter().fold(Level::Const, |l, a| Level::max(l, arg_level(a))),
        }
    }


    fn nth_operand(e: &Expr, n: usize) -> Option<Expr> {
        if n == 0 {
            return None;
        }
        match &e.kind {
            EKind::Conj(v) | EKind::Disj(v) | EKind::Tuple(v) | EKind::SetEnum(v) | EKind::Bi(_, v) => v.get(n - 1).cloned(),
            EKind::Apply(_, args) => match args.get(n - 1) {
                Some(Arg::Expr(x)) => Some(x.clone()),
                _ => None,
            },
            EKind::FcnApply(a, b) => match n {
                1 => Some(a.clone()),
                2 => Some(b.clone()),
                _ => None,
            },
            EKind::If(a, b, c) => match n {
                1 => Some(a.clone()),
                2 => Some(b.clone()),
                3 => Some(c.clone()),
                _ => None,
            },
            EKind::Label(_, _, x) | EKind::SubstIn(_, x) => Self::nth_operand(x, n),
            _ => None,
        }
    }

    fn body_operand(e: &Expr) -> Option<Expr> {
        match &e.kind {
            EKind::BQuant { body, .. }
            | EKind::UQuant { body, .. }
            | EKind::TQuant { body, .. }
            | EKind::Choose(_, _, body)
            | EKind::LetIn(_, body)
            | EKind::FcnCons(_, body) => Some(body.clone()),
            EKind::SubsetOf(_, _, p) => Some(p.clone()),
            EKind::SetOfAll(x, _) => Some(x.clone()),
            EKind::Label(_, _, x) | EKind::SubstIn(_, x) => Self::body_operand(x),
            _ => None,
        }
    }

    fn find_label(e: &Expr, name: &str) -> Option<Expr> {
        if let EKind::Label(n, _, inner) = &e.kind {
            if &**n == name {
                return Some(inner.clone());
            }
        }
        for c in e.children() {
            if let Some(x) = Self::find_label(&c, name) {
                return Some(x);
            }
        }
        None
    }

    /// `Def!sel1!sel2` : navigation into the body of a definition (labels, operand numbers, `<<`, `>>`, `:`)
    fn gen_selector(&mut self, g: &ast::GenId, args: Option<&Vec<ast::Expr>>, loc: Loc) -> Option<R<Expr>> {
        let mut path: Vec<(Name, Option<&Vec<ast::Expr>>)> = g.prefix.iter().map(|p| (p.name.clone(), p.args.as_ref())).collect();
        path.push((g.name.clone(), args));
        for k in (1..path.len()).rev() {
            let name: Vec<&str> = path[..k].iter().map(|p| &*p.0).collect();
            let compound = name.join("!");
            let d = match self.resolve(&compound) {
                Some(Sym::Def(d)) if d.kind == DefKind::User => d,
                _ => continue,
            };
            let mut cur = match d.body() {
                Some(b) => b,
                None => continue,
            };
            for (sel, _) in &path[k..] {
                let next = match &**sel {
                    "<<" => Self::nth_operand(&cur, 1),
                    ">>" => Self::nth_operand(&cur, 2),
                    ":" => Self::body_operand(&cur),
                    "@" => None,
                    t if t.chars().all(|c| c.is_ascii_digit()) => t.parse::<usize>().ok().and_then(|n| Self::nth_operand(&cur, n)),
                    t => Self::find_label(&cur, t),
                };
                match next {
                    Some(n) => cur = n,
                    None => {
                        let n = path.iter().map(|p| &*p.0).collect::<Vec<_>>().join("!");
                        return Some(Ok(self.mk(EKind::Unsupported(nm(&n)), loc, Level::Const)));
                    }
                }
            }
            // synthetic definition: same parameters as `d`, body = the selected subexpression
            let params = d.params.borrow().clone();
            let synth = new_def(nm(&path.iter().map(|p| &*p.0).collect::<Vec<_>>().join("!")), params, Some(cur), false, DefKind::User, self.cur_name.clone(), loc);
            self.finish_def_levels(&synth);
            let mut all_args: Vec<&ast::Expr> = Vec::new();
            for (_, a) in &path[..k] {
                if let Some(a) = a {
                    all_args.extend(a.iter());
                }
            }
            let sym = Sym::Def(synth.clone());
            let nme = synth.name.clone();
            let a = match self.gen_args_for(&sym, &nme, &all_args, loc) {
                Ok(a) => a,
                Err(()) => return Some(Err(())),
            };
            let c = Callee::Def(synth);
            let lv = self.apply_level(&c, &a);
            return Some(Ok(self.mk(EKind::Apply(c, a), loc, lv)));
        }
        None
    }

    /// `Thm!<<...`, `Thm!2`, `Thm!:`: navigation into a theorem/assumption (proof steps are not analysed)
    fn any_prefix_resolves(&mut self, g: &ast::GenId) -> bool {
        for k in (1..=g.prefix.len()).rev() {
            let name: Vec<&str> = g.prefix[..k].iter().map(|p| &*p.name).collect();
            if self.resolve(&name.join("!")).is_some() {
                return true;
            }
        }
        false
    }

    fn is_theorem_ref(&mut self, g: &ast::GenId) -> bool {
        for k in (1..=g.prefix.len()).rev() {
            let name: Vec<&str> = g.prefix[..k].iter().map(|p| &*p.name).collect();
            if let Some(Sym::Def(d)) = self.resolve(&name.join("!")) {
                if d.kind == DefKind::Theorem {
                    return true;
                }
            }
        }
        false
    }

    fn gen_id_appl(&mut self, g: &ast::GenId, args: Option<&Vec<ast::Expr>>, loc: Loc) -> R<Expr> {
        // `@`
        if g.prefix.is_empty() && &*g.name == "@" {
            if self.at_depth <= 0 {
                self.err(loc, "@ used where its meaning is not defined.");
                return Err(());
            }
            return Ok(self.mk(EKind::At, loc, Level::Const));
        }
        let compound = Self::compound_name(g);
        let mut all_args: Vec<&ast::Expr> = Vec::new();
        for p in &g.prefix {
            if let Some(a) = &p.args {
                all_args.extend(a.iter());
            }
        }
        if let Some(a) = args {
            all_args.extend(a.iter());
        }
        let sym = self.resolve(&compound);
        let sym = match sym {
            Some(s) => s,
            None if !g.prefix.is_empty() && self.is_theorem_ref(g) => {
                return Ok(self.mk(EKind::Bi(B::True, vec![]), loc, Level::Const));
            }
            None if !g.prefix.is_empty() => {
                if let Some(r) = self.gen_selector(g, args, loc) {
                    return r;
                }
                if self.any_prefix_resolves(g) {
                    return Ok(self.mk(EKind::Unsupported(nm(&compound)), loc, Level::Const));
                }
                self.err(loc, format!("Unknown operator: `{}'.", compound));
                return Err(());
            }
            None => {
                if g.kind == IdKind::Ident || !g.prefix.is_empty() {
                    self.err(loc, format!("Unknown operator: `{}'.", compound));
                } else {
                    self.err(loc, format!("Could not find declaration or definition of symbol '{}'.", compound));
                }
                return Err(());
            }
        };
        match &sym {
            Sym::Module(_) => {
                self.err(loc, format!("Module name '{}' used as operator.", compound));
                Err(())
            }
            Sym::Builtin(b) => {
                if all_args.len() != b.arity() {
                    self.arity_error(loc, &compound, b.arity());
                    return Err(());
                }
                let mut es = Vec::new();
                for a in &all_args {
                    es.push(self.gen_expr(a)?);
                }
                Ok(self.bi(*b, es, loc))
            }
            _ => {
                let a = self.gen_args_for(&sym, &compound, &all_args, loc)?;
                let callee = match &sym {
                    Sym::Def(d) => Callee::Def(d.clone()),
                    Sym::Decl(d) => Callee::Decl(d.clone()),
                    Sym::Param(p) => {
                        // recursion detection for `f[x \in S] == ... f[...] ...`
                        for (fp, flag) in &self.cur_fcn {
                            if Rc::ptr_eq(fp, p) {
                                flag.set(true);
                            }
                        }
                        Callee::Param(p.clone())
                    }
                    _ => unreachable!(),
                };
                let lv = self.apply_level(&callee, &a);
                Ok(self.mk(EKind::Apply(callee, a), loc, lv))
            }
        }
    }

    pub(crate) fn bi(&mut self, b: B, es: Vec<Expr>, loc: Loc) -> Expr {
        let (oplevel, maxl, w) = b.props();
        let mut l = oplevel;
        for (i, e) in es.iter().enumerate() {
            let k = i.min(1);
            if w[k] {
                l = Level::max(l, e.level);
            }
            if self.levels && (e.level as i32) > maxl[k] && !(b.arity() == 1 && i > 0) {
                self.err(
                    loc,
                    format!(
                        "Level error in applying operator {}:\nThe level of argument {} exceeds the maximum level allowed by the operator.",
                        b.name(),
                        i + 1
                    ),
                );
            }
        }
        self.mk(EKind::Bi(b, es), loc, l)
    }


    /// application of a prefix/infix/postfix operator symbol
    fn gen_op_app(&mut self, name: &str, oloc: Loc, loc: Loc, args: &[&ast::Expr], fix: &str) -> R<Expr> {
        let sym = self.resolve(name);
        match sym {
            None => {
                self.err(oloc, format!("Could not find declaration or definition of symbol '{}'.", name));
                self.err(loc, format!("Couldn't resolve {} operator symbol `{}'.", fix, name));
                for a in args {
                    let _ = self.gen_expr(a);
                }
                Err(())
            }
            Some(Sym::Builtin(b)) => {
                let mut es = vec![];
                let mut failed = false;
                for a in args {
                    match self.gen_expr(a) {
                        Ok(x) => es.push(x),
                        Err(()) => failed = true,
                    }
                }
                if failed {
                    return Err(());
                }
                Ok(self.bi(b, es, loc))
            }
            Some(Sym::Module(_)) => {
                self.err(loc, format!("Module name '{}' used as operator.", name));
                Err(())
            }
            Some(s) => {
                let a = self.gen_args_for(&s, name, args, loc)?;
                let c = match s {
                    Sym::Def(d) => Callee::Def(d),
                    Sym::Decl(d) => Callee::Decl(d),
                    Sym::Param(p) => Callee::Param(p),
                    _ => unreachable!(),
                };
                let lv = self.apply_level(&c, &a);
                Ok(self.mk(EKind::Apply(c, a), loc, lv))
            }
        }
    }

    pub(crate) fn gen_expr(&mut self, e: &ast::Expr) -> R<Expr> {
        use ast::ExprKind as K;
        let loc = e.loc;
        match &*e.kind {
            K::Num(t) => Ok(self.mk(EKind::Num(self.num_lit(t)), loc, Level::Const)),
            K::Real(a, b) => Ok(self.mk(EKind::Dec(a.clone(), b.clone()), loc, Level::Const)),
            K::Str(s) => {
                // `new StringNode(...)` interns the unquoted literal at semantic-analysis time
                crate::intern::intern(s);
                Ok(self.mk(EKind::Str(s.clone()), loc, Level::Const))
            }
            K::Id(g) => self.gen_id_appl(g, None, loc),
            K::Appl(g, args) => self.gen_id_appl(g, Some(args), loc),
            K::Paren(inner) => self.gen_expr(inner),
            K::Prefix(name, oloc, arg) => self.gen_op_app(name, *oloc, loc, &[&**arg], "prefix"),
            K::Postfix(arg, name, oloc) => self.gen_op_app(name, *oloc, loc, &[&**arg], "postfix"),
            K::Infix(l, name, oloc, r) => self.gen_op_app(name, *oloc, loc, &[&**l, &**r], "infix"),
            K::Times(items) => {
                let mut es = vec![];
                for i in items {
                    es.push(self.gen_expr(i)?);
                }
                let l = Self::maxl(&es);
                Ok(self.mk(EKind::Bi(B::Times, es), loc, l))
            }
            K::FcnAppl(f, args) => {
                let fe = self.gen_expr(f)?;
                let a = if args.len() == 1 {
                    self.gen_expr(&args[0])?
                } else {
                    let mut es = vec![];
                    for x in args {
                        es.push(self.gen_expr(x)?);
                    }
                    let l = Self::maxl(&es);
                    self.mk(EKind::Tuple(es), loc, l)
                };
                let l = Level::max(fe.level, a.level);
                Ok(self.mk(EKind::FcnApply(fe, a), loc, l))
            }
            K::Record(r, f) => {
                let re = self.gen_expr(r)?;
                let l = re.level;
                Ok(self.mk(EKind::Record(re, f.name.clone()), loc, l))
            }
            K::Tuple(items) => {
                let mut es = vec![];
                for i in items {
                    es.push(self.gen_expr(i)?);
                }
                let l = Self::maxl(&es);
                Ok(self.mk(EKind::Tuple(es), loc, l))
            }
            K::SetEnum(items) => {
                let mut es = vec![];
                for i in items {
                    es.push(self.gen_expr(i)?);
                }
                let l = Self::maxl(&es);
                Ok(self.mk(EKind::SetEnum(es), loc, l))
            }
            K::SubsetOf(v, set, pred) => {
                let s = self.gen_expr(set)?;
                self.push_scope();
                let bv = self.bound_vars(v);
                let p = self.gen_expr(pred);
                self.pop_scope();
                let p = p?;
                let l = Level::max(s.level, p.level);
                Ok(self.mk(EKind::SubsetOf(bv, s, p), loc, l))
            }
            K::SetOfAll(ex, bounds) => {
                self.push_scope();
                let r = (|| -> R<Expr> {
                    let groups = self.gen_bound_groups(bounds)?;
                    let x = self.gen_expr(ex)?;
                    let mut l = x.level;
                    for g in &groups {
                        l = Level::max(l, g.set.level);
                    }
                    Ok(self.mk(EKind::SetOfAll(x, groups), loc, l))
                })();
                self.pop_scope();
                r
            }
            K::FcnConst(bounds, body) => {
                self.push_scope();
                let r = (|| -> R<Expr> {
                    let groups = self.gen_bound_groups(bounds)?;
                    let x = self.gen_expr(body)?;
                    let mut l = x.level;
                    for g in &groups {
                        l = Level::max(l, g.set.level);
                    }
                    Ok(self.mk(EKind::FcnCons(groups, x), loc, l))
                })();
                self.pop_scope();
                r
            }
            K::SetOfFcns(a, b) => {
                let a = self.gen_expr(a)?;
                let b = self.gen_expr(b)?;
                let l = Level::max(a.level, b.level);
                Ok(self.mk(EKind::SetOfFcns(a, b), loc, l))
            }
            K::RcdCons(fields) | K::SetOfRcds(fields) => {
                let is_cons = matches!(&*e.kind, K::RcdCons(_));
                let mut seen = HashSet::new();
                let mut out = vec![];
                let mut l = Level::Const;
                let mut dup = false;
                for (id, ex) in fields {
                    if !seen.insert(id.name.clone()) {
                        dup = true;
                        self.err(id.loc, "Non-unique fields in constructor.");
                        continue;
                    }
                    let x = self.gen_expr(ex)?;
                    l = Level::max(l, x.level);
                    out.push((id.name.clone(), x));
                }
                if dup {
                    return Err(());
                }
                Ok(self.mk(if is_cons { EKind::RcdCons(out) } else { EKind::SetOfRcds(out) }, loc, l))
            }
            K::Except(f, specs) => {
                let fe = self.gen_expr(f)?;
                let mut out = vec![];
                let mut l = fe.level;
                for s in specs {
                    let mut path = vec![];
                    for c in &s.path {
                        match c {
                            ast::ExceptComp::Field(id) => path.push(ExceptComp::Field(id.name.clone())),
                            ast::ExceptComp::Index(ix) => {
                                let mut v = vec![];
                                for x in ix {
                                    let xe = self.gen_expr(x)?;
                                    l = Level::max(l, xe.level);
                                    v.push(xe);
                                }
                                path.push(ExceptComp::Index(v));
                            }
                        }
                    }
                    self.at_depth += 1;
                    let val = self.gen_expr(&s.val);
                    self.at_depth -= 1;
                    let val = val?;
                    l = Level::max(l, val.level);
                    out.push(ExceptSpec { path, val });
                }
                Ok(self.mk(EKind::Except(fe, out), loc, l))
            }
            K::ActionExpr { boxed, act, sub } => {
                let a = self.gen_expr(act)?;
                let s = self.gen_expr(sub)?;
                Ok(self.mk(EKind::ActionSub { boxed: *boxed, act: a, sub: s }, loc, Level::Action))
            }
            K::Fairness { strong, sub, act } => {
                let s = self.gen_expr(sub)?;
                let a = self.gen_expr(act)?;
                Ok(self.mk(EKind::Fair { strong: *strong, sub: s, act: a }, loc, Level::Temporal))
            }
            K::If(c, t, f) => {
                let c = self.gen_expr(c)?;
                let t = self.gen_expr(t)?;
                let f = self.gen_expr(f)?;
                let l = Level::max(c.level, Level::max(t.level, f.level));
                Ok(self.mk(EKind::If(c, t, f), loc, l))
            }
            K::Case(arms, other) => {
                let mut out = vec![];
                let mut l = Level::Const;
                for (c, v) in arms {
                    let ce = self.gen_expr(c)?;
                    let ve = self.gen_expr(v)?;
                    l = Level::max(l, Level::max(ce.level, ve.level));
                    out.push((ce, ve));
                }
                let o = match other {
                    Some(o) => {
                        let oe = self.gen_expr(o)?;
                        l = Level::max(l, oe.level);
                        Some(oe)
                    }
                    None => None,
                };
                Ok(self.mk(EKind::Case(out, o), loc, l))
            }
            K::LetIn(items, body) => {
                self.push_scope();
                self.let_level += 1;
                let mut defs: Vec<Rc<OpDef>> = Vec::new();
                let node = self.cur.clone().unwrap();
                let pending_before = self.pending_rec.len();
                for it in items {
                    match it {
                        LetItem::Def(d) => {
                            let _ = match &d.body {
                                DefBody::Expr(_) => self.process_operator(d, &node, Some(&mut defs)).map(|_| ()),
                                DefBody::Function(..) => self.process_function(d, &node, Some(&mut defs)).map(|_| ()),
                                DefBody::Instance(i) => self.process_module_definition(d, i, &node, Some(&mut defs)).map(|_| ()),
                            };
                        }
                        LetItem::Recursive(decls, _) => self.process_recursive(decls),
                    }
                }
                let pend: Vec<Rc<OpDef>> = self.pending_rec.drain(pending_before..).collect();
                for p in pend {
                    if !p.is_defined.get() {
                        self.err(p.loc, format!("Recursive operator {} was declared but never defined.", p.name));
                    }
                }
                let b = self.gen_expr(body);
                self.let_level -= 1;
                self.pop_scope();
                let b = b?;
                let l = b.level;
                Ok(self.mk(EKind::LetIn(defs, b), loc, l))
            }
            K::Quant { forall, temporal, binds, body } => {
                self.push_scope();
                let r = (|| -> R<Expr> {
                    match binds {
                        QBinds::Bound(bs) => {
                            let groups = self.gen_bound_groups(bs)?;
                            let b = self.gen_expr(body)?;
                            let mut l = b.level;
                            for g in &groups {
                                l = Level::max(l, g.set.level);
                            }
                            Ok(self.mk(EKind::BQuant { forall: *forall, bounds: groups, body: b }, loc, l))
                        }
                        QBinds::Unbound(ids) => {
                            let mut ps = vec![];
                            for id in ids {
                                let p = new_param(id.name.clone(), 0, id.loc);
                                self.add_symbol(id.name.clone(), Sym::Param(p.clone()), id.loc);
                                ps.push(p);
                            }
                            let b = self.gen_expr(body)?;
                            if *temporal {
                                Ok(self.mk(EKind::TQuant { forall: *forall, params: ps, body: b }, loc, Level::Temporal))
                            } else {
                                let l = b.level;
                                Ok(self.mk(EKind::UQuant { forall: *forall, params: ps, body: b }, loc, l))
                            }
                        }
                    }
                })();
                self.pop_scope();
                r
            }
            K::Choose { var, set, body } => {
                let s = match set {
                    Some(s) => Some(self.gen_expr(s)?),
                    None => None,
                };
                self.push_scope();
                let bv = self.bound_vars(var);
                let b = self.gen_expr(body);
                self.pop_scope();
                let b = b?;
                let l = Level::max(b.level, s.as_ref().map_or(Level::Const, |x| x.level));
                Ok(self.mk(EKind::Choose(bv, s, b), loc, l))
            }
            K::Conj(items) | K::Disj(items) => {
                let mut es = vec![];
                for i in items {
                    es.push(self.gen_expr(i)?);
                }
                let l = Self::maxl(&es);
                Ok(self.mk(if matches!(&*e.kind, K::Conj(_)) { EKind::Conj(es) } else { EKind::Disj(es) }, loc, l))
            }
            K::Label(lbl, inner) => {
                let mut ps = vec![];
                for p in &lbl.params {
                    if let Some(Sym::Param(prm)) = self.resolve(&p.name) {
                        ps.push(prm);
                    }
                }
                let b = self.gen_expr(inner)?;
                let l = b.level;
                Ok(self.mk(EKind::Label(lbl.name.name.clone(), ps, b), loc, l))
            }
            K::Lambda(..) => {
                self.err(loc, "LAMBDA expression used where an expression is required.");
                Err(())
            }
        }
    }
}

#[allow(dead_code)]
fn _unused(_: Shape) {
    let _ = ops::resolve_synonym;
}
