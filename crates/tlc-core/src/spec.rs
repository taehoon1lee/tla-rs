//! Port of `tlc2.tool.impl.SpecProcessor` (+ the relevant parts of `Spec`/`Tool`'s constructor): turns the semantic
//! graph and the `.cfg` into the pieces the model checker needs (variables, Init, Next, invariants, constraints ...).

use crate::compile::Compiler;
use crate::config::ModelConfig;
use crate::ec;
use crate::eval::Ev;
use crate::ir::*;
use crate::natives;
use crate::value::*;
use std::cell::Cell;
use std::collections::HashSet;
use std::rc::Rc;
use tla_sany::analyze::SemSpec;
use tla_sany::sem::{self, Callee, EKind, B};

#[derive(Debug, Clone)]
pub struct SetupErr {
    pub code: i32,
    pub text: String,
}

fn serr<T>(code: i32, text: impl Into<String>) -> Result<T, SetupErr> {
    Err(SetupErr { code, text: text.into() })
}

/// a compiled top-level expression with the size of its frame
pub struct Top {
    pub name: String,
    pub ex: Ex,
    pub nslots: Rc<Cell<usize>>,
    pub loc: tla_sany::ast::Loc,
    pub module: String,
}

pub struct Setup {
    pub ev: Rc<Ev>,
    pub comp: Compiler,
    pub vars: Vec<Rc<sem::OpDecl>>,
    pub init: Vec<Top>,
    pub next: Vec<Top>,
    pub invariants: Vec<Top>,
    pub constraints: Vec<Top>,
    pub action_constraints: Vec<Top>,
    pub assumes: Vec<(Top, String)>,
    pub view: Option<Top>,
    pub symmetry: Option<Top>,
    pub check_deadlock: bool,
    /// temporal formulas to be checked (PROPERTY) and fairness of the spec (liveness)
    pub properties: Vec<(String, sem::Expr)>,
    pub spec_temporal: Vec<sem::Expr>,
    /// names and locations of the "actions" (top-level disjuncts of Next) for trace labels
    pub root: Rc<sem::ModuleNode>,
}

fn lookup_def(root: &Rc<sem::ModuleNode>, name: &str) -> Option<Rc<sem::OpDef>> {
    match root.lookup(name) {
        Some(sem::Sym::Def(d)) => Some(d),
        _ => None,
    }
}

impl Setup {
    pub fn run_top(&self, t: &Top, s0: &[Value], s1: &[Value]) -> R<Value> {
        self.ev.with_frame(t.nslots.get(), |ev| ev.eval(&t.ex, s0, s1))
    }
}

pub fn setup(sem: &SemSpec, cfg: &ModelConfig, set_bound: i64) -> Result<Setup, SetupErr> {
    let root = sem.root.clone();
    let vars: Vec<Rc<sem::OpDecl>> = root.variables();
    let ev = Ev::new(vars.len());
    ev.set_bound.set(set_bound);
    *ev.var_names.borrow_mut() = vars.iter().map(|v| v.name.clone()).collect();
    let mut comp = Compiler::new(natives::lookup);
    for (i, v) in vars.iter().enumerate() {
        comp.var_index.insert(v.id, i as u32);
    }
    // declarations substituted by some INSTANCE
    for m in sem.modules.values() {
        for inst in m.instances.borrow().iter() {
            for s in &inst.subs {
                comp.substitutable.insert(s.target.id);
            }
        }
    }

    // ---- constants of the root module
    let consts = root.constants();
    let mut used_cfg: HashSet<String> = HashSet::new();
    for d in &consts {
        let name = d.name.to_string();
        if let Some((_, rhs)) = cfg.overrides.iter().find(|(l, _)| *l == name) {
            used_cfg.insert(name.clone());
            match lookup_def(&root, rhs) {
                Some(def) => {
                    comp.const_ops.insert(d.id, def.clone());
                }
                None => {
                    return serr(
                        ec::TLC_CONFIG_WRONG_SUBSTITUTION,
                        format!("The configuration file substitutes for {} with the undefined identifier {}.", name, rhs),
                    )
                }
            }
            continue;
        }
        match cfg.constants.iter().find(|c| c.name == name) {
            Some(c) => {
                used_cfg.insert(name.clone());
                comp.const_values.insert(d.id, c.value.clone());
                ev.consts.borrow_mut().insert(d.id, c.value.clone());
            }
            None => {
                return serr(
                    ec::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM,
                    format!("The constant parameter {} is not assigned a value by the configuration file.", name),
                )
            }
        }
    }
    // constants / overrides naming definitions of the root module
    for c in &cfg.constants {
        if used_cfg.contains(&c.name) {
            continue;
        }
        match lookup_def(&root, &c.name) {
            Some(def) => {
                comp.def_values.insert(def.id, c.value.clone());
                used_cfg.insert(c.name.clone());
            }
            None => {
                return serr(
                    ec::TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC,
                    format!("In the configuration file, the identifier {} does not appear in the specification.", c.name),
                )
            }
        }
    }
    for (l, r) in &cfg.overrides {
        if used_cfg.contains(l) {
            continue;
        }
        let ldef = match lookup_def(&root, l) {
            Some(d) => d,
            None => {
                return serr(
                    ec::TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC,
                    format!("In the configuration file, the identifier {} does not appear in the specification.", l),
                )
            }
        };
        match lookup_def(&root, r) {
            Some(rdef) => {
                if rdef.arity() != ldef.arity() {
                    return serr(
                        ec::TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS,
                        format!("The configuration file substitutes for {} with the identifier {}, which has a different number of arguments.", l, r),
                    );
                }
                comp.overrides.insert(ldef.id, rdef);
            }
            None => {
                return serr(
                    ec::TLC_CONFIG_WRONG_SUBSTITUTION,
                    format!("The configuration file substitutes for {} with the undefined identifier {}.", l, r),
                )
            }
        }
    }
    // module-specific overrides
    for (m, ovs) in &cfg.mod_overrides {
        let module = match sem.modules.get(m) {
            Some(x) => x.clone(),
            None => return serr(ec::TLC_NO_MODULES, format!("The module {} is not defined in the specification.", m)),
        };
        for (l, r) in ovs {
            match (lookup_def(&module, l), lookup_def(&module, r).or_else(|| lookup_def(&root, r))) {
                (Some(ld), Some(rd)) => {
                    comp.overrides.insert(ld.id, rd);
                }
                _ => {
                    return serr(
                        ec::TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC,
                        format!("In the configuration file, the identifier {} does not appear in the specification.", l),
                    )
                }
            }
        }
    }
    for (m, cs) in &cfg.mod_constants {
        let module = match sem.modules.get(m) {
            Some(x) => x.clone(),
            None => return serr(ec::TLC_NO_MODULES, format!("The module {} is not defined in the specification.", m)),
        };
        for c in cs {
            match lookup_def(&module, &c.name) {
                Some(def) => {
                    comp.def_values.insert(def.id, c.value.clone());
                }
                None => {
                    return serr(
                        ec::TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC,
                        format!("In the configuration file, the identifier {} does not appear in the specification.", c.name),
                    )
                }
            }
        }
    }

    let mut setup = Setup {
        ev: ev.clone(),
        comp,
        vars,
        init: vec![],
        next: vec![],
        invariants: vec![],
        constraints: vec![],
        action_constraints: vec![],
        assumes: vec![],
        view: None,
        symmetry: None,
        check_deadlock: cfg.check_deadlock.unwrap_or(true),
        properties: vec![],
        spec_temporal: vec![],
        root: root.clone(),
    };

    // ---- INIT / NEXT / SPECIFICATION
    if !cfg.spec.is_empty() {
        if !cfg.init.is_empty() || !cfg.next.is_empty() {
            return serr(ec::TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT, "The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields.");
        }
        let def = match lookup_def(&root, &cfg.spec) {
            Some(d) => d,
            None => {
                return serr(
                    ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                    format!("The name {} specified in the configuration file\nis not defined in the specification.", cfg.spec),
                )
            }
        };
        if def.arity() != 0 {
            return serr(ec::TLC_CONFIG_ID_REQUIRES_NO_ARG, format!("TLC requires {} not to take any argument.", cfg.spec));
        }
        let body = def.body();
        let mut inits: Vec<sem::Expr> = vec![];
        let mut nexts: Vec<(sem::Expr, String)> = vec![];
        let mut temporals: Vec<sem::Expr> = vec![];
        if let Some(b) = body {
            analyze_spec_formula(&b, &mut inits, &mut nexts, &mut temporals, 0);
        }
        for e in inits {
            let (ex, n) = setup.comp.compile_top(&e);
            setup.init.push(Top { name: "Init".into(), ex, nslots: n, loc: e.loc, module: def.module.to_string() });
        }
        if nexts.len() > 1 {
            return serr(ec::TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS, "TLC cannot handle the specification: it has more than one next-state relation.");
        }
        for (e, name) in nexts {
            let (ex, n) = setup.comp.compile_top(&e);
            setup.next.push(Top { name, ex, nslots: n, loc: e.loc, module: def.module.to_string() });
        }
        setup.spec_temporal = temporals;
    } else {
        if cfg.init.is_empty() {
            return serr(ec::TLC_CONFIG_MISSING_INIT, "The configuration file did not specify the initial state predicate.");
        }
        if cfg.next.is_empty() {
            return serr(ec::TLC_CONFIG_MISSING_NEXT, "The configuration file did not specify the next state predicate.");
        }
        for (what, name, is_init) in [("initial predicate", &cfg.init, true), ("next state action", &cfg.next, false)] {
            let def = match lookup_def(&root, name) {
                Some(d) => d,
                None => match root.lookup(name) {
                    Some(sem::Sym::Decl(_)) => {
                        return serr(ec::TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, format!("The {} {} cannot be a constant.", what, name))
                    }
                    _ => {
                        return serr(
                            ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                            format!("The {} {} specified in the configuration file\nis not defined in the specification.", what, name),
                        )
                    }
                },
            };
            if def.arity() != 0 {
                return serr(ec::TLC_CONFIG_ID_REQUIRES_NO_ARG, format!("TLC requires {} {} not to take any argument.", what, name));
            }
            let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
            let (ex, n) = setup.comp.compile_top(&e);
            let top = Top { name: name.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string() };
            if is_init {
                setup.init.push(top);
            } else {
                setup.next.push(top);
            }
        }
    }

    // ---- invariants
    for name in cfg.invariants.iter().chain(std::iter::empty()) {
        let def = match lookup_def(&root, name) {
            Some(d) => d,
            None => {
                return serr(
                    ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                    format!("The invariant {} specified in the configuration file\nis not defined in the specification.", name),
                )
            }
        };
        if def.arity() != 0 {
            return serr(ec::TLC_CONFIG_ID_REQUIRES_NO_ARG, format!("TLC requires invariant {} not to take any argument.", name));
        }
        if def.level.get() > sem::Level::State {
            return serr(
                ec::TLC_INVARIANT_VIOLATED_LEVEL,
                format!("The invariant {} is not a state predicate (one with no primes or temporal operators).", name),
            );
        }
        let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
        let (ex, n) = setup.comp.compile_top(&e);
        setup.invariants.push(Top { name: name.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string() });
    }
    for src in [&cfg.constraints, &cfg.action_constraints] {
        let is_action = std::ptr::eq(src, &cfg.action_constraints);
        for name in src.iter() {
            let kind = if is_action { "action constraint" } else { "constraint" };
            let def = match lookup_def(&root, name) {
                Some(d) => d,
                None => {
                    return serr(
                        ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                        format!("The {} {} specified in the configuration file\nis not defined in the specification.", kind, name),
                    )
                }
            };
            if def.arity() != 0 {
                return serr(ec::TLC_CONFIG_ID_REQUIRES_NO_ARG, format!("TLC requires {} {} not to take any argument.", kind, name));
            }
            let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
            let (ex, n) = setup.comp.compile_top(&e);
            let top = Top { name: name.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string() };
            if is_action {
                setup.action_constraints.push(top);
            } else {
                setup.constraints.push(top);
            }
        }
    }
    if !cfg.view.is_empty() {
        if let Some(def) = lookup_def(&root, &cfg.view) {
            let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
            let (ex, n) = setup.comp.compile_top(&e);
            setup.view = Some(Top { name: cfg.view.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string() });
        } else {
            return serr(
                ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                format!("The view {} specified in the configuration file\nis not defined in the specification.", cfg.view),
            );
        }
    }
    if !cfg.symmetry.is_empty() {
        if let Some(def) = lookup_def(&root, &cfg.symmetry) {
            let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
            let (ex, n) = setup.comp.compile_top(&e);
            setup.symmetry = Some(Top { name: cfg.symmetry.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string() });
        } else {
            return serr(
                ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                format!("The symmetry {} specified in the configuration file\nis not defined in the specification.", cfg.symmetry),
            );
        }
    }
    for name in &cfg.properties {
        let def = match lookup_def(&root, name) {
            Some(d) => d,
            None => {
                return serr(
                    ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                    format!("The property {} specified in the configuration file\nis not defined in the specification.", name),
                )
            }
        };
        if let Some(b) = def.body() {
            setup.properties.push((name.clone(), b));
        }
    }
    // ---- assumptions
    let assumes: Vec<Rc<sem::AssumeNode>> = root.assumes.borrow().clone();
    for a in assumes {
        let (ex, n) = setup.comp.compile_top(&a.expr);
        let desc = format!("line {}, col {} to line {}, col {} of module {}", a.loc.bl, a.loc.bc, a.loc.el, a.loc.ec, a.module);
        setup.assumes.push((Top { name: desc.clone(), ex, nslots: n, loc: a.loc, module: a.module.to_string() }, desc));
    }
    // constant operators: resolve the definitions given by `<-` for constant parameters with arguments
    for (id, def) in setup.comp.const_ops.clone() {
        let cd = setup.comp.compile_def(&def);
        ev.const_ops.borrow_mut().insert(id, cd);
    }
    Ok(setup)
}

/// Port of `SpecProcessor.processConfigSpec`: split the temporal formula `Spec` into the initial predicate(s), the
/// next-state relation and the remaining (fairness) conjuncts.
fn analyze_spec_formula(e: &sem::Expr, inits: &mut Vec<sem::Expr>, nexts: &mut Vec<(sem::Expr, String)>, temporals: &mut Vec<sem::Expr>, depth: usize) {
    if depth > 50 {
        return;
    }
    match &e.kind {
        EKind::Conj(items) => {
            for x in items {
                analyze_spec_formula(x, inits, nexts, temporals, depth + 1);
            }
        }
        EKind::Bi(B::And, items) => {
            for x in items {
                analyze_spec_formula(x, inits, nexts, temporals, depth + 1);
            }
        }
        EKind::Apply(Callee::Def(d), args) if args.is_empty() && e.level >= sem::Level::Temporal => {
            if let Some(b) = d.body() {
                analyze_spec_formula(&b, inits, nexts, temporals, depth + 1);
            }
        }
        EKind::SubstIn(_, b) | EKind::Label(_, _, b) => analyze_spec_formula(b, inits, nexts, temporals, depth + 1),
        EKind::Bi(B::Always, args) => match &args[0].kind {
            EKind::ActionSub { boxed: true, act, .. } => {
                let name = match &act.kind {
                    EKind::Apply(Callee::Def(d), a) if a.is_empty() => d.name.to_string(),
                    _ => "Next".to_string(),
                };
                nexts.push((act.clone(), name));
            }
            _ => temporals.push(e.clone()),
        },
        _ => {
            if e.level <= sem::Level::State {
                inits.push(e.clone());
            } else {
                temporals.push(e.clone());
            }
        }
    }
}
