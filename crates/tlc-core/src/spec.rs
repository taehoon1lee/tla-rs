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
use std::collections::{HashMap, HashSet};
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
    /// values of the bound variables the expression was compiled with (they occupy the first slots)
    pub bound: Vec<Value>,
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
    /// Java: `constraint.toString()` of the model constraints / action constraints (location of the expression), for the error 2215
    pub constraint_exprs: Vec<String>,
    pub action_constraint_exprs: Vec<String>,
    pub assumes: Vec<(Top, String)>,
    pub view: Option<Top>,
    /// Java: `allParams` of the VIEW expression: the variables (by declaration index) and the number of constants it depends on
    pub view_params: (Vec<u32>, usize),
    /// Java: `ALIAS`: the record printed instead of the state variables in error traces
    pub alias: Option<Top>,
    pub symmetry: Option<Top>,
    /// the SYMMETRY definition and the configuration's `Spec <- Replacement` names (for warning 2300)
    pub symmetry_def: Option<Rc<sem::OpDef>>,
    pub override_rev: HashMap<String, String>,
    pub check_deadlock: bool,
    /// temporal formulas to be checked (PROPERTY) and fairness of the spec (liveness)
    /// temporal properties (checked by the liveness checker)
    pub properties: Vec<(String, sem::Expr)>,
    /// the bound variables (constant arguments of operators, unrolled `\A`) each temporal property was reached with
    pub properties_bound: Vec<Vec<(Rc<sem::Param>, Value)>>,
    /// state-level properties `P` (checked in the initial states) / action properties `[][A]_v` (checked on every step)
    pub implied_inits: Vec<Top>,
    pub implied_actions: Vec<Top>,
    /// the temporal parts of the PROPERTYs: (name in the configuration file, location, module)
    pub implied_temporals: Vec<(String, tla_sany::ast::Loc, String)>,
    /// POSTCONDITION definitions (constant level), checked after the state space has been explored
    /// (compiled definition, location text, is a `_POSSIBLE` check)
    pub postconditions: Vec<(Top, String, bool)>,
    pub spec_temporal: Vec<sem::Expr>,
    /// the SPECIFICATION of the configuration and the location of its definition (for warning 2259)
    pub spec_name: String,
    pub spec_loc: String,
    /// orders of solution of the temporal properties (`Liveness.processLiveness`), filled by the driver
    pub live: crate::liveness::oos::LiveSpec,
    /// names and locations of the "actions" (top-level disjuncts of Next) for trace labels
    pub root: Rc<sem::ModuleNode>,
}

fn sem_body_loc(d: &Rc<sem::OpDef>) -> tla_sany::ast::Loc {
    match d.body() {
        Some(b) => b.loc,
        None => d.loc,
    }
}

fn lookup_def(root: &Rc<sem::ModuleNode>, name: &str) -> Option<Rc<sem::OpDef>> {
    match root.lookup(name) {
        Some(sem::Sym::Def(d)) => Some(d),
        _ => None,
    }
}

impl Setup {
    pub fn run_top(&self, t: &Top, s0: &[Value], s1: &[Value]) -> R<Value> {
        self.ev.epoch.set(self.ev.epoch.get() + 1);
        self.ev.with_frame(t.nslots.get().max(t.bound.len()), |ev| {
            for (i, v) in t.bound.iter().enumerate() {
                ev.set_slot(i as u32, Slot::V(v.clone()));
            }
            ev.eval(&t.ex, s0, s1)
        })
    }
}

/// analyses a module generated at run time against the specification's module table (see `tla_sany::analyze_generated_module`)
pub type ModuleAnalyzer<'a> = &'a dyn Fn(&str) -> Result<Rc<sem::ModuleNode>, String>;

thread_local! {
    /// operators replaced by the user's Java classes: `(module, operator, arity, value)` (see `classfile::load_user_overrides`)
    static USER_OVERRIDES: std::cell::RefCell<Vec<(String, String, usize, Value)>> = const { std::cell::RefCell::new(Vec::new()) };
}

pub fn set_user_overrides(v: Vec<(String, String, usize, Value)>) {
    USER_OVERRIDES.with(|u| *u.borrow_mut() = v);
}

pub fn setup(sem: &SemSpec, cfg: &ModelConfig, set_bound: i64, seed: i64, analyze: ModuleAnalyzer) -> Result<Setup, SetupErr> {
    let root = sem.root.clone();
    // Java: `ModuleNode.getVariableDecls` lists the variables in the order of the `Hashtable` that holds the symbols of the module (reversed
    // enumeration order = ascending bucket index, `String.hashCode() % capacity`, oldest first within a bucket); the capacity follows
    // from the number of symbols (the 72 built-in operators of TLA+ are in every module's table)
    let mut vars: Vec<Rc<sem::OpDecl>> = root.variables();
    java_decl_order(&mut vars, &root, |v| v.name.to_string());
    let ev = Ev::new(vars.len());
    ev.set_bound.set(set_bound);
    ev.seed.set(seed);
    *ev.var_names.borrow_mut() = vars.iter().map(|v| v.name.clone()).collect();
    let mut comp = Compiler::new(natives::lookup);
    for (i, v) in vars.iter().enumerate() {
        comp.var_index.insert(v.id, i as u32);
    }
    // Java: `SpecProcessor.processModuleOverrides`: the user's Java methods replace the operators of the module they match
    USER_OVERRIDES.with(|u| {
        for (module, op, arity, value) in u.borrow().iter() {
            if let Some(m) = sem.modules.get(module) {
                for d in m.defs.borrow().iter() {
                    if *d.module == **module && *d.name == **op && d.params.borrow().len() == *arity {
                        comp.def_values.insert(d.id, value.clone());
                    }
                }
            }
        }
    });
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
        // `CONSTANT F(0) = 1  F(1) = 2`: the lines of an operator form its table (Java: SpecProcessor.makeConstantTable)
        let rows: Vec<&crate::config::ConstAssign> = cfg.constants.iter().filter(|c| c.name == name && !c.args.is_empty()).collect();
        if !rows.is_empty() {
            used_cfg.insert(name.clone());
            let arity = rows[0].args.len();
            if rows.iter().any(|r| r.args.len() != arity) {
                return serr(ec::TLC_CONFIG_OP_ARITY_INCONSISTENT, format!("The operator {} is assigned values with inconsistent numbers of arguments.", name));
            }
            ev.const_tables.borrow_mut().insert(d.id, Rc::new(rows.iter().map(|r| (r.args.clone(), r.value.clone())).collect()));
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
            None => {}
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
        constraint_exprs: vec![],
        action_constraint_exprs: vec![],
        assumes: vec![],
        view: None,
        view_params: (vec![], 0),
        alias: None,
        symmetry: None,
        symmetry_def: None,
        override_rev: cfg.overrides.iter().map(|(l, r)| (r.clone(), l.clone())).collect(),
        check_deadlock: cfg.check_deadlock.unwrap_or(true),
        properties: vec![],
        properties_bound: vec![],
        implied_inits: vec![],
        implied_actions: vec![],
        implied_temporals: vec![],
        postconditions: vec![],
        spec_temporal: vec![],
        live: Default::default(),
        spec_name: String::new(),
        spec_loc: String::new(),
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
        setup.spec_name = cfg.spec.clone();
        setup.spec_loc = format!("line {}, col {} to line {}, col {} of module {}", def.loc.bl, def.loc.bc, def.loc.el, def.loc.ec, def.module);
        let mut inits: Vec<sem::Expr> = vec![];
        let mut nexts: Vec<(sem::Expr, String)> = vec![];
        let mut temporals: Vec<sem::Expr> = vec![];
        if let Some(b) = body {
            // Java: SpecProcessor.processConfigSpec: a name that is neither an operator nor a Boolean (a state variable)
            // cannot be used as a spec
            let mut cur = b.clone();
            for _ in 0..50 {
                match &cur.kind {
                    EKind::Apply(Callee::Def(d), a) if a.is_empty() && d.arity() == 0 => match d.body() {
                        Some(nb) => cur = nb,
                        None => break,
                    },
                    EKind::Apply(Callee::Decl(dd), a) if a.is_empty() && matches!(dd.kind, sem::DeclKind::Variable) => {
                        return serr(
                            ec::TLC_CONFIG_OP_IS_EQUAL,
                            format!(
                                "The operator {}, which equals line {}, col {} to line {}, col {} of module {},
cannot be used as a spec",
                                dd.name, dd.loc.bl, dd.loc.bc, dd.loc.el, dd.loc.ec, dd.module
                            ),
                        );
                    }
                    _ => break,
                }
            }
            SPEC_ERR.with(|c| *c.borrow_mut() = None);
            SUBSCRIPTS.with(|v| v.borrow_mut().clear());
            SPEC_STACK.with(|v| v.borrow_mut().clear());
            SPEC_TAGS.with(|v| v.borrow_mut().clear());
            SPEC_WARNINGS.with(|v| v.borrow_mut().clear());
            SPEC_PROPS.with(|v| *v.borrow_mut() = cfg.properties.clone());
            analyze_spec_formula(&b, &mut inits, &mut nexts, &mut temporals, 0);
            for (code, text) in SPEC_WARNINGS.with(|v| v.borrow_mut().drain(..).collect::<Vec<_>>()) {
                pending_warning(code, text);
            }
            // Java: processConfigSpec: the subscript collector follows definitions (and the definitions configured for them); a cycle through `<-` overrides ends in a StackOverflowError
            let subs: Vec<sem::Expr> = SUBSCRIPTS.with(|v| v.borrow().clone());
            if subs.iter().any(|x| subscript_overflows(&setup.comp.overrides, x, 0)) {
                return serr(ec::SYSTEM_STACK_OVERFLOW, "stack overflow while collecting the variables of a subscript");
            }
            if let Some(loc) = SPEC_ERR.with(|c| c.borrow_mut().take()) {
                return serr(ec::TLC_LIVE_CANNOT_HANDLE_FORMULA, format!("TLC cannot handle the temporal formula {}{}", loc, def.module));
            }
            // Java: processConfigSpec: a conjunct that is a constant Boolean is no initial predicate: FALSE makes the spec trivially false
            let mut kept: Vec<sem::Expr> = Vec::with_capacity(inits.len());
            for e in inits.drain(..) {
                if let EKind::Apply(Callee::Def(d), a) = &e.kind {
                    // (a definition that reads variables, or applies a parameterized INSTANCE whose level SANY cannot narrow to
                    // constant, fails to evaluate here and stays an initial predicate)
                    if a.is_empty() && e.level <= sem::Level::State && !mentions_tlcget(&e, &mut vec![], 0) {
                        let r = {
                            let mut tr = crate::liveness::translate::Translator::new(&mut setup);
                            tr.eval_const(&e)
                        };
                        match r {
                            Ok(Value::Bool(false)) => {
                                return serr(ec::TLC_CONFIG_SPEC_IS_TRIVIAL, format!("The spec is trivially false because {} is false.", d.name))
                            }
                            Ok(Value::Bool(true)) => continue,
                            _ => {}
                        }
                    }
                }
                kept.push(e);
            }
            inits = kept;
        }
        if !inits.is_empty() {
            let e = if inits.len() == 1 {
                // Java: `processConfigSpec` takes the body of a definition without parameters as the initial predicate
                let x = inits.pop().unwrap();
                match &x.kind {
                    EKind::Apply(Callee::Def(d), a) if a.is_empty() => sem::Expr::new(x.kind.clone(), d.loc, x.level),
                    _ => x,
                }
            } else {
                let loc = inits[0].loc;
                let lvl = inits.iter().fold(sem::Level::Const, |a, x| sem::Level::max(a, x.level));
                sem::Expr::new(EKind::Conj(inits), loc, lvl)
            };
            let (ex, n) = setup.comp.compile_top(&e);
            setup.init.push(Top { name: "Init".into(), ex, nslots: n, loc: e.loc, module: def.module.to_string(), bound: vec![] });
        }
        if nexts.len() > 1 {
            return serr(ec::TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS, "TLC cannot handle the specification: it has more than one next-state relation.");
        }
        for (e, name) in nexts {
            // Java: the next-state relation of a SPECIFICATION is the body of the definition (`getActions` follows a definition without arguments)
            let e = match &e.kind {
                EKind::Apply(Callee::Def(d), a) if a.is_empty() => sem::Expr::new(e.kind.clone(), d.loc, e.level),
                _ => e,
            };
            // the action's source position names the module the relation is written in
            let saved_module = std::mem::replace(&mut setup.comp.cur_module, def.module.clone());
            let (ex, n) = setup.comp.compile_top(&e);
            setup.comp.cur_module = saved_module;
            setup.next.push(Top { name, ex, nslots: n, loc: e.loc, module: def.module.to_string(), bound: vec![] });
        }
        setup.spec_temporal = temporals;
    } else {
        let has_vars = !setup.vars.is_empty();
        if cfg.init.is_empty() {
            if has_vars || !cfg.invariants.is_empty() || !cfg.properties.is_empty() {
                return serr(ec::TLC_CONFIG_MISSING_INIT, "The configuration file did not specify the initial state predicate.");
            }
        }
        if cfg.next.is_empty() {
            if (!cfg.init.is_empty() || has_vars) && (!cfg.invariants.is_empty() || !cfg.properties.is_empty()) {
                return serr(ec::TLC_CONFIG_MISSING_NEXT, "The configuration file did not specify the next state predicate.");
            }
        }
        for (what, name, is_init) in [("initial predicate", &cfg.init, true), ("next state action", &cfg.next, false)] {
            if name.is_empty() {
                continue;
            }
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
            let top = Top { name: name.clone(), ex, nslots: n, loc: sem_body_loc(&def), module: def.module.to_string(), bound: vec![] };
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
        let top = Top { name: name.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] };
        // Java: processConfigInvariants: a constant-level definition is a value; TRUE is only worth a warning, anything else is an error
        if def.level.get() == sem::Level::Const {
            let undef = vec![Value::Undef; setup.vars.len()];
            match setup.run_top(&top, &undef, &setup.ev.empty()) {
                Ok(Value::Bool(true)) => {
                    pending_warning(ec::TLC_INVARIANT_CONSTANT_LEVEL, format!("The invariant {} is a constant-level formula (i.e., it contains no variables, primes, or temporal operators) and evaluates to {}. To assert constant-level formulas in your spec, use ASSUME ConstInv. If you optionally want to give the assumption a name, write ASSUME YourAssumption == ConstInv instead. See https://explain.tlapl.us/assumptions-and-invariants for additional details.", name, "TRUE"));
                    continue;
                }
                Ok(v) => {
                    return serr(ec::TLC_CONFIG_ID_HAS_VALUE, format!("The invariant of {} is equal to {}", name, v.to_tla()));
                }
                Err(_) => {}
            }
        }
        setup.invariants.push(top);
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
            let top = Top { name: name.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] };
            let bl = sem_body_loc(&def);
            let text = format!("line {}, col {} to line {}, col {} of module {}", bl.bl, bl.bc, bl.el, bl.ec, def.original().module);
            if is_action {
                setup.action_constraints.push(top);
                setup.action_constraint_exprs.push(text);
            } else {
                setup.constraints.push(top);
                setup.constraint_exprs.push(text);
            }
        }
    }
    if !cfg.view.is_empty() {
        if let Some(def) = lookup_def(&root, &cfg.view) {
            let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
            let (ex, n) = setup.comp.compile_top(&e);
            setup.view = Some(Top { name: cfg.view.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] });
            let mut vs: Vec<u32> = vec![];
            let mut nconst = 0usize;
            let mut seen: Vec<usize> = vec![];
            if let Some(b) = def.body() {
                collect_params(&b, &setup.vars, &mut vs, &mut nconst, &mut seen, 0);
            }
            vs.sort_unstable();
            vs.dedup();
            setup.view_params = (vs, nconst);
        } else {
            return serr(
                ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                format!("The view {} specified in the configuration file\nis not defined in the specification.", cfg.view),
            );
        }
    }
    if !cfg.alias.is_empty() {
        if let Some(def) = lookup_def(&root, &cfg.alias) {
            let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
            let (ex, n) = setup.comp.compile_top(&e);
            setup.alias = Some(Top { name: cfg.alias.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] });
        }
    }
    if !cfg.symmetry.is_empty() {
        if let Some(def) = lookup_def(&root, &cfg.symmetry) {
            let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
            let (ex, n) = setup.comp.compile_top(&e);
            setup.symmetry_def = Some(def.clone());
            setup.symmetry = Some(Top { name: cfg.symmetry.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] });
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
                    format!("The property {} specified in the configuration file
is not defined in the specification.", name),
                )
            }
        };
        if def.arity() != 0 {
            return serr(ec::TLC_CONFIG_ID_REQUIRES_NO_ARG, format!("TLC requires property {} not to take any argument.", name));
        }
        // Java: processConfig: a state-level formula is only checked in the initial states
        if def.level.get() == sem::Level::State {
            pending_warning(ec::TLC_LIVE_FORMULA_STATE_LEVEL, format!("The formula {0} is a state-level formula, but it was used as a PROPERTY (or PROPERTIES), where a temporal formula is typically expected. State-level formulas used as PROPERTY or PROPERTIES are only checked in the initial state. To verify that the formula {0} holds in all states of every behavior, use INVARIANT {0} instead. Alternatively, applying the \"always\" temporal operator ([]) to the state-level formula {0} changes it into a temporal formula, asserting that {0} holds in all states of every behavior. See https://explain.tlapl.us/invariants-and-properties for additional details.", name));
        }
        if let Some(b) = def.body() {
            let mut wraps: Vec<Rc<Vec<sem::Subst>>> = vec![];
            let mut bound: Vec<(Rc<sem::Param>, Value)> = vec![];
            classify_property(&mut setup, name, name, &b, &def, &mut wraps, &mut bound, 0)?;
        }
    }
    // Java: processConfig: `PROPERTY L` with a SPECIFICATION whose temporal conjuncts all come from `L` checks `S /\ L => L`
    if !cfg.spec.is_empty() && cfg.properties.len() == 1 {
        let tags: Vec<bool> = SPEC_TAGS.with(|t| t.borrow().clone());
        if !tags.is_empty() && tags.iter().all(|&b| b) {
            if let (Some(ldef), Some(sdef)) = (lookup_def(&root, &cfg.properties[0]), lookup_def(&root, &cfg.spec)) {
                let loc = |d: &Rc<sem::OpDef>| format!("line {}, col {} to line {}, col {} of module {}", d.loc.bl, d.loc.bc, d.loc.el, d.loc.ec, d.original().module);
                let text = format!("Implied-temporal checking is a tautology.\nThe temporal formula {0} at {1} equals\nthe fairness constraints of the behavior specification {2} at {3}.\nTherefore, checking whether {2} => {0} using TLC will never result in a violation of {0}.", cfg.properties[0], loc(&ldef), cfg.spec, loc(&sdef));
                pending_warning(ec::TLC_LIVE_FORMULA_AND_FAIRNESS_TAUTOLOGY, text);
            }
        }
    }
    // ---- postconditions
    for name in &cfg.postconditions {
        let def = match lookup_def(&root, name) {
            Some(d) => d,
            None => {
                return serr(
                    ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                    format!("The postcondition {} specified in the configuration file
is not defined in the specification.", name),
                )
            }
        };
        let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
        let (ex, n) = setup.comp.compile_top(&e);
        let loc = sem_body_loc(&def);
        let text = format!("line {}, col {} to line {}, col {} of module {}", loc.bl, loc.bc, loc.el, loc.ec, def.original().module);
        setup.postconditions.push((Top { name: name.clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] }, text, false));
    }
    process_config_possible(&mut setup, &root, cfg, analyze)?;
    // ---- assumptions
    let assumes: Vec<Rc<sem::AssumeNode>> = root.assumes.borrow().clone();
    for a in assumes {
        let (ex, n) = setup.comp.compile_top(&a.expr);
        // Java: `assumps[i].toString()` is the location of the assumption EXPRESSION (without `ASSUME [Name ==]`).
        let l = a.expr.loc;
        let desc = format!("line {}, col {} to line {}, col {} of module {}", l.bl, l.bc, l.el, l.ec, a.module);
        setup.assumes.push((Top { name: desc.clone(), ex, nslots: n, loc: l, module: a.module.to_string(), bound: vec![] }, desc));
    }
    // constant operators: resolve the definitions given by `<-` for constant parameters with arguments
    for (id, def) in setup.comp.const_ops.clone() {
        let cd = setup.comp.compile_def(&def);
        ev.const_ops.borrow_mut().insert(id, cd);
    }
    // Java: SpecProcessor.processConstantDefns evaluates the definition a constant is substituted with once at startup; a failure
    // is an error only if the definition is not constant-level (it reads variables or TLCGet)
    ev.setup_phase.set(true);
    let mut const_decls = root.constants();
    java_decl_order(&mut const_decls, &root, |d| d.name.to_string());
    let mut const_defs: Vec<(usize, Rc<sem::OpDef>)> = vec![];
    for d in &const_decls {
        if let Some(def) = setup.comp.const_ops.get(&d.id) {
            const_defs.push((d.id, def.clone()));
        }
    }
    for (id, def) in const_defs {
        if def.arity() != 0 {
            continue;
        }
        let body = match def.body() {
            Some(b) => b,
            None => continue,
        };
        if def.level.get() == sem::Level::Const && !mentions_tlcget(&body, &mut vec![], 0) {
            continue;
        }
        let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
        let (ex, n) = setup.comp.compile_top(&e);
        let top = Top { name: def.name.to_string(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] };
        if let Err(err) = setup.run_top(&top, &ev.empty(), &ev.empty()) {
            ev.setup_phase.set(false);
            // Java: `TLCGet` is an `@Evaluation` override: its failure comes back as the error of the override that produced it
            let err = if err.code == ec::TLC_MODULE_TLCGET_UNDEFINED {
                let mut w = err.clone();
                w.msg = format!("@!@!@STARTMSG 2154:0 @!@!@\nAttempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLCGetSet.TLCGetEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel),\nbut it produced the following error:\n{}\n@!@!@ENDMSG 2154 @!@!@", err.java_message());
                w
            } else {
                err
            };
            let cname = root.constants().iter().find(|d| d.id == id).map(|d| d.name.to_string()).unwrap_or_default();
            return serr(
                ec::TLC_CONFIG_SUBSTITUTION_NON_CONSTANT,
                format!("The configuration file substitutes constant {} with non-constant {} - specifically: {}", cname, def.name, err.msg),
            );
        }
    }
    // Java: SpecProcessor.processConstantDefns: every definition without parameters whose level is constant is evaluated once at startup, in
    // the order the context of the root module lists them (an INSTANCE contributes its copies in the order of a `Hashtable`); a failure
    // is swallowed and the definition is evaluated again where it is used
    {
        fn collect(m: &Rc<sem::ModuleNode>, out: &mut Vec<Rc<sem::OpDef>>, seen: &mut HashSet<usize>) {
            for e in m.extends.borrow().iter() {
                if !e.is_standard.get() && seen.insert(Rc::as_ptr(e) as usize) {
                    collect(e, out, seen);
                }
            }
            out.extend(m.defs.borrow().iter().cloned());
        }
        let mut defs: Vec<Rc<sem::OpDef>> = vec![];
        collect(&root, &mut defs, &mut HashSet::new());
        for def in defs {
            if def.arity() != 0 || def.level.get() != sem::Level::Const || def.kind != sem::DefKind::User || def.in_let.get() {
                continue;
            }
            match def.body() {
                Some(b) if !mentions_tlcget(&b, &mut vec![], 0) => {}
                _ => continue,
            }
            let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
            let (ex, n) = setup.comp.compile_top(&e);
            let top = Top { name: def.name.to_string(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] };
            let _ = setup.run_top(&top, &ev.empty(), &ev.empty());
        }
    }
    ev.setup_phase.set(false);
    // source info for action labels
    *setup.ev.node_info.borrow_mut() = std::mem::take(&mut setup.comp.node_info).into_iter().collect();
    setup.ev.warnings.borrow_mut().extend(take_pending_warnings());
    Ok(setup)
}

/// Java: `Context` keeps its symbols in a `Hashtable`; `getVariableDecls` / `getConstantDecls` list them in reverse enumeration order
/// (ascending bucket index = `String.hashCode() % capacity`, oldest first within a bucket).  The capacity follows from the number of symbols
/// (the 72 built-in operators of TLA+ are in every module's table).
fn java_decl_order<T>(items: &mut [T], root: &sem::ModuleNode, name: impl Fn(&T) -> String) {
    let n = root.ctx.borrow().items.len() + 72;
    let mut cap: usize = 11;
    let mut thr = cap * 3 / 4;
    while n > thr {
        cap = cap * 2 + 1;
        thr = cap * 3 / 4;
    }
    let java_hash = |s: &str| -> i32 { s.chars().fold(0i32, |h, c| h.wrapping_mul(31).wrapping_add(c as i32)) };
    items.sort_by_key(|x| ((java_hash(&name(x)) & 0x7fff_ffff) as usize) % cap);
}

/// the variables and constants an expression depends on, through the definitions it applies (Java: `SemanticNode.getAllParams`)
fn collect_params(e: &sem::Expr, vars: &[Rc<sem::OpDecl>], out: &mut Vec<u32>, nconst: &mut usize, seen: &mut Vec<usize>, depth: u32) {
    if depth > 60 {
        return;
    }
    match &e.kind {
        EKind::Apply(Callee::Decl(d), _) => {
            match vars.iter().position(|v| v.id == d.id) {
                Some(i) => out.push(i as u32),
                None => {
                    if !seen.contains(&d.id) {
                        seen.push(d.id);
                        *nconst += 1;
                    }
                }
            }
            return;
        }
        EKind::Apply(Callee::Def(d), args) => {
            for a in args {
                if let sem::Arg::Expr(x) = a {
                    collect_params(x, vars, out, nconst, seen, depth + 1);
                }
            }
            if !seen.contains(&d.id) {
                seen.push(d.id);
                if let Some(b) = d.body() {
                    collect_params(&b, vars, out, nconst, seen, depth + 1);
                }
            }
            return;
        }
        _ => {}
    }
    for c in e.children() {
        collect_params(&c, vars, out, nconst, seen, depth + 1);
    }
}

/// does `e` refer to a formal parameter of an operator?
fn mentions_param(e: &sem::Expr, depth: u32) -> bool {
    if depth > 40 {
        return false;
    }
    if matches!(&e.kind, EKind::Apply(Callee::Param(_), _)) {
        return true;
    }
    e.children().iter().any(|c| mentions_param(c, depth + 1))
}

/// does `e` (or a definition it calls) apply `TLC!TLCGet`? (Java: `TLCGet` has `minLevel = 1`, i.e. it is not constant)
fn mentions_tlcget(e: &sem::Expr, seen: &mut Vec<usize>, depth: u32) -> bool {
    if depth > 40 {
        return false;
    }
    if let EKind::Apply(Callee::Def(d), args) = &e.kind {
        // Java: the `@Evaluation(minLevel = 1)` operators: their level bound is that of a state expression
        let o = d.original();
        if (&*o.module == "TLC" && &*o.name == "TLCGet") || (&*o.module == "TLCExt" && matches!(&*o.name, "Trace" | "CounterExample")) {
            return true;
        }
        for a in args {
            if let sem::Arg::Expr(x) = a {
                if mentions_tlcget(x, seen, depth + 1) {
                    return true;
                }
            }
        }
        if !seen.contains(&d.id) {
            seen.push(d.id);
            if let Some(b) = d.body() {
                if mentions_tlcget(&b, seen, depth + 1) {
                    return true;
                }
            }
        }
        return false;
    }
    e.children().iter().any(|c| mentions_tlcget(c, seen, depth + 1))
}

/// Port of `SpecProcessor.processConfigProps`: split a PROPERTY into invariants (`[]P`), implied actions
/// (`[][A]_v`), implied initial predicates and temporal formulas.  `bound` is the Java `Context`: the constant arguments
/// operators were called with and the elements of unrolled `\A` quantifiers.
#[allow(clippy::too_many_arguments)]
thread_local! {
    /// the names of the operators applied on the way to the formula being analysed by `analyze_rec` (Java: the `stack` of `processConfigSpec`)
    static SPEC_STACK: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
    /// the PROPERTY names of the configuration (for the tautology warning) and, per temporal conjunct of the specification, whether it was
    /// reached through an application of one of them
    static SPEC_PROPS: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
    static SPEC_TAGS: std::cell::RefCell<Vec<bool>> = const { std::cell::RefCell::new(Vec::new()) };
    /// warnings found while the specification is analysed
    static SPEC_WARNINGS: std::cell::RefCell<Vec<(i32, String)>> = const { std::cell::RefCell::new(Vec::new()) };
}

thread_local! {
    /// warnings of the setup that is running (they are printed even when the setup fails later)
    static PENDING_WARNINGS: std::cell::RefCell<Vec<(i32, String)>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn pending_warning(code: i32, text: String) {
    PENDING_WARNINGS.with(|w| w.borrow_mut().push((code, text)));
}

pub fn take_pending_warnings() -> Vec<(i32, String)> {
    PENDING_WARNINGS.with(|w| w.borrow_mut().drain(..).collect())
}

fn push_temporal(temporals: &mut Vec<sem::Expr>, e: sem::Expr) {
    let tagged = SPEC_STACK.with(|s| SPEC_PROPS.with(|p| s.borrow().iter().any(|n| p.borrow().contains(n))));
    SPEC_TAGS.with(|t| t.borrow_mut().push(tagged));
    temporals.push(e);
}

thread_local! {
    /// location of the `INSTANCE` statement a substitution list (by address) stems from, for the nodes `wrap_all` builds
    static WRAP_LOCS: std::cell::RefCell<HashMap<usize, tla_sany::ast::Loc>> = std::cell::RefCell::new(HashMap::new());
}

thread_local! {
    /// formal parameters of operators inlined by `classify_property` that stand for a non-constant argument formula
    static PROP_ENV: std::cell::RefCell<Vec<(usize, sem::Expr)>> = const { std::cell::RefCell::new(Vec::new()) };
}

thread_local! {
    /// arguments of operator applications met while the SPECIFICATION is analysed: parameter id -> argument expression
    static INLINE_PARAMS: std::cell::RefCell<HashMap<usize, sem::Expr>> = std::cell::RefCell::new(HashMap::new());
}

/// the argument expression a parameter that is not bound in the frame being compiled stands for (see `analyze_apply`)
pub fn inline_param(id: usize) -> Option<sem::Expr> {
    INLINE_PARAMS.with(|m| m.borrow().get(&id).cloned())
}

pub fn register_inline_param(id: usize, x: sem::Expr) {
    INLINE_PARAMS.with(|m| m.borrow_mut().insert(id, x));
}

thread_local! {
    /// definitions passed for operator parameters (same purpose as `INLINE_PARAMS`)
    static INLINE_OPS: std::cell::RefCell<HashMap<usize, Rc<sem::OpDef>>> = std::cell::RefCell::new(HashMap::new());
}

pub fn register_inline_op(id: usize, d: Rc<sem::OpDef>) {
    INLINE_OPS.with(|m| m.borrow_mut().insert(id, d));
}

pub fn inline_op(id: usize) -> Option<Rc<sem::OpDef>> {
    INLINE_OPS.with(|m| m.borrow().get(&id).cloned())
}

thread_local! {
    /// the name the next inlined operator application is reported with (an operator parameter bound to a definition)
    static PROP_NAME: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

thread_local! {
    /// operator parameters of inlined operators that are bound to a definition
    static PROP_OPS: std::cell::RefCell<Vec<(usize, Rc<sem::OpDef>)>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn classify_property(
    setup: &mut Setup,
    cfg_name: &str,
    name: &str,
    e: &sem::Expr,
    owner: &Rc<sem::OpDef>,
    wraps: &mut Vec<Rc<Vec<sem::Subst>>>,
    bound: &mut Vec<(Rc<sem::Param>, Value)>,
    depth: usize,
) -> Result<(), SetupErr> {
    if depth > 100 {
        return Ok(());
    }
    let mk_top = |setup: &mut Setup, nm: &str, x: &sem::Expr, wraps: &[Rc<Vec<sem::Subst>>], bound: &[(Rc<sem::Param>, Value)]| -> Top {
        let w = wrap_all(x, wraps);
        let params: Vec<Rc<sem::Param>> = bound.iter().map(|(p, _)| p.clone()).collect();
        // Java: the nodes of the formula are located in the module that defines the operator it came from
        let saved_module = std::mem::replace(&mut setup.comp.cur_module, owner.original().module.clone());
        let (ex, n) = setup.comp.compile_top_bound(&w, &params);
        setup.comp.cur_module = saved_module;
        Top { name: nm.to_string(), ex, nslots: n, loc: x.loc, module: owner.module.to_string(), bound: bound.iter().map(|(_, v)| v.clone()).collect() }
    };
    let push_prop = |setup: &mut Setup, _nm: &str, x: &sem::Expr, wraps: &[Rc<Vec<sem::Subst>>], bound: &[(Rc<sem::Param>, Value)]| {
        setup.properties.push((cfg_name.to_string(), wrap_all(x, wraps)));
        setup.implied_temporals.push((cfg_name.to_string(), x.loc, owner.module.to_string()));
        setup.properties_bound.push(bound.to_vec());
    };
    match &e.kind {
        EKind::SubstIn(subs, b) => {
            WRAP_LOCS.with(|m| m.borrow_mut().insert(Rc::as_ptr(subs) as usize, e.loc));
            wraps.push(subs.clone());
            let r = classify_property(setup, cfg_name, name, b, owner, wraps, bound, depth + 1);
            wraps.pop();
            return r;
        }
        EKind::Label(_, _, b) => return classify_property(setup, cfg_name, name, b, owner, wraps, bound, depth + 1),
        // Java: a formal parameter reached while analysing an inlined operator body is a LazyValue: continue with the
        // argument expression (Github817c/d, LetDef1Boxed)
        EKind::Apply(Callee::Param(p), args) if args.is_empty() => {
            let arg = PROP_ENV.with(|env| env.borrow().iter().rev().find(|(id, _)| *id == p.id).map(|(_, x)| x.clone()));
            if let Some(x) = arg {
                return classify_property(setup, cfg_name, name, &x, owner, wraps, bound, depth + 1);
            }
        }
        // an operator parameter bound to a definition: apply that definition to the arguments
        EKind::Apply(Callee::Param(p), args) if !args.is_empty() => {
            let od = PROP_OPS.with(|ops| ops.borrow().iter().rev().find(|(id, _)| *id == p.id).map(|(_, d)| d.clone()));
            if let Some(od) = od {
                let call = sem::Expr::new(EKind::Apply(Callee::Def(od), args.clone()), e.loc, e.level);
                // Java names the property after the operator as written at the call site: the parameter
                PROP_NAME.with(|n| *n.borrow_mut() = Some(p.name.to_string()));
                let r = classify_property(setup, cfg_name, name, &call, owner, wraps, bound, depth + 1);
                PROP_NAME.with(|n| *n.borrow_mut() = None);
                return r;
            }
        }
        EKind::Apply(Callee::Def(d), args) if args.is_empty() && d.kind != sem::DefKind::ModuleInstance => {
            if let Some(b) = d.body() {
                // a definition: recurse with its name
                return classify_property(setup, cfg_name, &d.name.to_string(), &b, d, wraps, bound, depth + 1);
            }
        }
        // Java: a call of a non-recursive operator with constant arguments is replaced by its body (`getOpContext`)
        EKind::Apply(Callee::Def(d), args) if !args.is_empty() && wraps.is_empty() && !d.in_recursive.get() && d.arity() == args.len() => {
            if let Some(b) = d.body() {
                let params = d.params.borrow().clone();
                let mut vals: Vec<(Rc<sem::Param>, Value)> = vec![];
                let mut lazy: Vec<(usize, sem::Expr)> = vec![];
                let mut lazy_ops: Vec<(usize, Rc<sem::OpDef>)> = vec![];
                let mut ok = true;
                for (p, a) in params.iter().zip(args.iter()) {
                    match a {
                        // an argument that is not a constant (a temporal formula, ...) is kept as an expression
                        // (only a literal temporal formula: the other forms are handled by the translation of the property)
                        sem::Arg::Expr(x) if x.level != sem::Level::Const && matches!(x.kind, EKind::Bi(B::Always, _)) => lazy.push((p.id, x.clone())),
                        // a definition passed for an operator parameter
                        sem::Arg::Op(sem::OpArg::Callee(Callee::Def(od), _)) => lazy_ops.push((p.id, od.clone())),
                        sem::Arg::Expr(x) if x.level == sem::Level::Const => {
                            let r = {
                                let mut tr = crate::liveness::translate::Translator::new(setup);
                                tr.set_bound(bound.clone());
                                tr.eval_const(x)
                            };
                            match r {
                                Ok(v) => vals.push((p.clone(), v)),
                                Err(_) => {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    let n0 = bound.len();
                    bound.extend(vals);
                    let e0 = PROP_ENV.with(|env| env.borrow().len());
                    PROP_ENV.with(|env| env.borrow_mut().extend(lazy));
                    let o0 = PROP_OPS.with(|ops| ops.borrow().len());
                    PROP_OPS.with(|ops| ops.borrow_mut().extend(lazy_ops));
                    let shown = PROP_NAME.with(|n| n.borrow_mut().take()).unwrap_or_else(|| d.name.to_string());
                    let r = classify_property(setup, cfg_name, &shown, &b, d, wraps, bound, depth + 1);
                    PROP_OPS.with(|ops| ops.borrow_mut().truncate(o0));
                    PROP_ENV.with(|env| env.borrow_mut().truncate(e0));
                    bound.truncate(n0);
                    return r;
                }
            }
        }
        // Java: OPCODE_bf: a bounded `\A` over constant sets is unrolled into one property per context
        EKind::BQuant { forall: true, bounds, body } => {
            let ctxs = {
                let mut tr = crate::liveness::translate::Translator::new(setup);
                tr.set_bound(bound.clone());
                tr.contexts(bounds)
            };
            if let Ok(ctxs) = ctxs {
                if ctxs.is_empty() {
                    return serr(ec::TLC_LIVE_FORMULA_TAUTOLOGY, "Temporal formula is a tautology (its negation is unsatisfiable).");
                }
                let nm = format!("line {}, col {} to line {}, col {} of module {}", body.loc.bl, body.loc.bc, body.loc.el, body.loc.ec, owner.original().module);
                for ctx in ctxs {
                    let n0 = bound.len();
                    bound.extend(ctx);
                    let r = classify_property(setup, cfg_name, &nm, body, owner, wraps, bound, depth + 1);
                    bound.truncate(n0);
                    r?;
                }
                return Ok(());
            }
        }
        EKind::Conj(items) | EKind::Bi(B::And, items) => {
            for x in items {
                // Java: `conj.toString()` is the source location of the conjunct
                let nm = format!("line {}, col {} to line {}, col {} of module {}", x.loc.bl, x.loc.bc, x.loc.el, x.loc.ec, owner.original().module);
                classify_property(setup, cfg_name, &nm, x, owner, wraps, bound, depth + 1)?;
            }
            return Ok(());
        }
        EKind::Bi(B::Always, args) => {
            let x = &args[0];
            match &x.kind {
                EKind::ActionSub { boxed: true, .. } => {
                    let t = mk_top(setup, name, x, wraps, bound);
                    setup.implied_actions.push(t);
                    return Ok(());
                }
                _ if x.level < sem::Level::Action => {
                    let nm = match &x.kind {
                        EKind::Apply(Callee::Def(d), a) if a.is_empty() => d.name.to_string(),
                        _ => name.to_string(),
                    };
                    let t = mk_top(setup, &nm, x, wraps, bound);
                    setup.invariants.push(t);
                    return Ok(());
                }
                _ => {
                    push_prop(setup, name, e, wraps, bound);
                    return Ok(());
                }
            }
        }
        _ => {}
    }
    match e.level {
        sem::Level::Const | sem::Level::State => {
            let t = mk_top(setup, name, e, wraps, bound);
            setup.implied_inits.push(t);
        }
        sem::Level::Temporal => push_prop(setup, name, e, wraps, bound),
        _ => {
            let (code, kind) = match &e.kind {
                EKind::ActionSub { boxed: true, .. } => (ec::TLC_CONFIG_PROPERTY_ACTION_LEVEL_SQUARE_A_SUB_V, 1),
                EKind::ActionSub { boxed: false, .. } => (ec::TLC_CONFIG_PROPERTY_ACTION_LEVEL_ANGLE_A_SUB_V, 2),
                _ => (ec::TLC_CONFIG_PROPERTY_ACTION_LEVEL, 0),
            };
            // Java: MP: the three texts share their first sentences and differ in the advice
            let at = format!("line {}, col {} to line {}, col {} of module {}", e.loc.bl, e.loc.bc, e.loc.el, e.loc.ec, owner.module);
            let head = format!(
                "The formula {} at {} is an action-level formula (i.e., it contains no temporal operators). Only temporal-level (or state-level) formulas are allowed under PROPERTY or PROPERTIES. ",
                name, at
            );
            let advice = match kind {
                1 => format!(
                    "To check that action {} holds in *every* step of the behavior, define a temporal property by applying the \"always\" temporal operator ([]) to the formula at {} (compare page 90 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).",
                    name, at
                ),
                2 => format!(
                    "To check that infinitely many {} steps occur, define a temporal property by applying the \"always eventually\" temporal operator combination ([]<>) to the formula at {} (compare page 91 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).",
                    name, at
                ),
                _ => format!(
                    "To check that action {} holds in *every* step of the behavior, define a temporal property: Let A be the formula at {}; rewrite A as [][A]_v, where v is a state function (typically the tuple of variables) (compare page 90 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).",
                    name, at
                ),
            };
            return serr(code, format!("{}{}", head, advice));
        }
    }
    Ok(())
}

/// Port of `SpecProcessor.processConfigSpec`: split the temporal formula `Spec` into the initial predicate(s), the
/// next-state relation and the remaining (fairness) conjuncts. INSTANCE substitutions met on the way wrap the parts.
thread_local! {
    /// the subscripts of the `[][A]_v` conjuncts `analyze_rec` met
    static SUBSCRIPTS: std::cell::RefCell<Vec<sem::Expr>> = const { std::cell::RefCell::new(Vec::new()) };
}

thread_local! {
    /// the first formula `analyze_rec` found that TLC cannot handle in a SPECIFICATION (location text without the module)
    static SPEC_ERR: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

/// does following the definitions (after the `<-` overrides) of a subscript never end?
fn subscript_overflows(ov: &HashMap<usize, Rc<sem::OpDef>>, e: &sem::Expr, depth: u32) -> bool {
    if depth > 400 {
        return true;
    }
    match &e.kind {
        EKind::Apply(Callee::Def(d), a) if a.is_empty() => {
            let d2 = ov.get(&d.id).or_else(|| ov.get(&d.original().id)).cloned().unwrap_or_else(|| d.clone());
            match d2.body() {
                Some(b) => subscript_overflows(ov, &b, depth + 1),
                None => false,
            }
        }
        EKind::Tuple(items) => items.iter().any(|x| subscript_overflows(ov, x, depth + 1)),
        _ => false,
    }
}

fn analyze_spec_formula(e: &sem::Expr, inits: &mut Vec<sem::Expr>, nexts: &mut Vec<(sem::Expr, String)>, temporals: &mut Vec<sem::Expr>, depth: usize) {
    let mut wraps: Vec<Rc<Vec<sem::Subst>>> = vec![];
    let mut env: Vec<(usize, EnvVal)> = vec![];
    analyze_rec(e, inits, nexts, temporals, depth, &mut wraps, &mut env);
}


#[derive(Clone)]
enum EnvVal {
    Expr(sem::Expr),
    Op(Rc<sem::OpDef>),
}

#[allow(clippy::too_many_arguments)]
fn analyze_apply(
    d: &Rc<sem::OpDef>,
    args: &[sem::Arg],
    inits: &mut Vec<sem::Expr>,
    nexts: &mut Vec<(sem::Expr, String)>,
    temporals: &mut Vec<sem::Expr>,
    depth: usize,
    wraps: &mut Vec<Rc<Vec<sem::Subst>>>,
    env: &mut Vec<(usize, EnvVal)>,
) {
    let params = d.params.borrow().clone();
    let n0 = env.len();
    for (p, a) in params.iter().zip(args.iter()) {
        match a {
            sem::Arg::Expr(x) => {
                // Java: `getOpContext` binds the argument to the parameter; the pieces of the specification found below are
                // compiled outside of the call, where such a parameter is replaced by its argument (call by name)
                INLINE_PARAMS.with(|m| m.borrow_mut().insert(p.id, x.clone()));
                env.push((p.id, EnvVal::Expr(x.clone())))
            }
            sem::Arg::Op(sem::OpArg::Callee(Callee::Def(od), _)) => env.push((p.id, EnvVal::Op(od.clone()))),
            sem::Arg::Op(sem::OpArg::Callee(Callee::Param(q), _)) => {
                // pass an operator parameter on
                if let Some(v) = env.iter().rev().find(|(id, _)| *id == q.id).map(|(_, v)| v.clone()) {
                    env.push((p.id, v));
                }
            }
            _ => {}
        }
    }
    if let Some(b) = d.body() {
        analyze_rec(&b, inits, nexts, temporals, depth + 1, wraps, env);
    }
    env.truncate(n0);
}

fn wrap_all(e: &sem::Expr, wraps: &[Rc<Vec<sem::Subst>>]) -> sem::Expr {
    let mut cur = e.clone();
    for w in wraps.iter().rev() {
        let level = cur.level;
        let loc = WRAP_LOCS.with(|m| m.borrow().get(&(Rc::as_ptr(w) as usize)).copied()).unwrap_or(cur.loc);
        cur = sem::Expr::new(EKind::SubstIn(w.clone(), cur), loc, level);
    }
    cur
}

fn analyze_rec(
    e: &sem::Expr,
    inits: &mut Vec<sem::Expr>,
    nexts: &mut Vec<(sem::Expr, String)>,
    temporals: &mut Vec<sem::Expr>,
    depth: usize,
    wraps: &mut Vec<Rc<Vec<sem::Subst>>>,
    env: &mut Vec<(usize, EnvVal)>,
) {
    if depth > 50 {
        return;
    }
    match &e.kind {
        EKind::Conj(items) | EKind::Bi(B::And, items) => {
            for x in items {
                analyze_rec(x, inits, nexts, temporals, depth + 1, wraps, env);
            }
        }
        // a parameter standing for a formula (`id(Init /\ [][Next]_vars)`): continue with the argument
        EKind::Apply(Callee::Param(p), args) if args.is_empty() => match env.iter().rev().find(|(id, _)| *id == p.id).map(|(_, v)| v.clone()) {
            Some(EnvVal::Expr(a)) => analyze_rec(&a, inits, nexts, temporals, depth + 1, wraps, env),
            _ => push_temporal(temporals, wrap_all(e, wraps)),
        },
        // an operator parameter applied to arguments: continue with the operator bound to it
        EKind::Apply(Callee::Param(p), args) if !args.is_empty() => match env.iter().rev().find(|(id, _)| *id == p.id).map(|(_, v)| v.clone()) {
            Some(EnvVal::Op(d)) => analyze_apply(&d, args, inits, nexts, temporals, depth, wraps, env),
            _ => push_temporal(temporals, wrap_all(e, wraps)),
        },
        EKind::Apply(Callee::Def(d), args) if args.is_empty() && e.level >= sem::Level::Temporal => {
            if let Some(b) = d.body() {
                SPEC_STACK.with(|s| s.borrow_mut().push(d.name.to_string()));
                analyze_rec(&b, inits, nexts, temporals, depth + 1, wraps, env);
                SPEC_STACK.with(|s| s.borrow_mut().pop());
            }
        }
        EKind::Apply(Callee::Def(d), args) if !args.is_empty() && e.level >= sem::Level::Temporal => {
            analyze_apply(d, args, inits, nexts, temporals, depth, wraps, env);
        }
        EKind::LetIn(_, b) => analyze_rec(b, inits, nexts, temporals, depth + 1, wraps, env),
        EKind::SubstIn(subs, b) => {
            wraps.push(subs.clone());
            analyze_rec(b, inits, nexts, temporals, depth + 1, wraps, env);
            wraps.pop();
        }
        EKind::Label(_, _, b) => analyze_rec(b, inits, nexts, temporals, depth + 1, wraps, env),
        EKind::Bi(B::Always, args) => match &args[0].kind {
            EKind::ActionSub { boxed: true, act, sub } => {
                SUBSCRIPTS.with(|v| v.borrow_mut().push(sub.clone()));
                // Java: processConfigSpec evaluates the substitutions of the enclosing INSTANCEs in the context of the specification, where the
                // parameters of a parameterized instance are not bound: the subscript cannot be examined (a warning, then the check is skipped)
                if wraps.iter().any(|w| w.iter().any(|s| match &s.value {
                    sem::Arg::Expr(x) => mentions_param(x, 0),
                    _ => false,
                })) {
                    SPEC_WARNINGS.with(|w| w.borrow_mut().push((crate::ec::TLC_COULD_NOT_DETERMINE_SUBSCRIPT, "TLC could not determine if the subscript of the next-state relation contains\nall state variables. Proceed with fingers crossed.".to_string())));
                }
                let name = match &act.kind {
                    EKind::Apply(Callee::Def(d), a) if a.is_empty() => d.name.to_string(),
                    // Java: an action that is not a definition is named "Action"
                    _ => "Action".to_string(),
                };
                nexts.push((wrap_all(act, wraps), name));
            }
            _ => {
                // Java: processConfigSpec: TLC cannot handle []S where S is a constant- or state-level formula
                if args[0].level <= sem::Level::State {
                    let l = args[0].loc;
                    SPEC_ERR.with(|c| {
                        if c.borrow().is_none() {
                            *c.borrow_mut() = Some(format!("line {}, col {} to line {}, col {} of module {}", l.bl, l.bc, l.el, l.ec, "")); 
                        }
                    });
                }
                push_temporal(temporals, wrap_all(e, wraps))
            }
        },
        _ => {
            if e.level <= sem::Level::State {
                inits.push(wrap_all(e, wraps));
            } else {
                push_temporal(temporals, wrap_all(e, wraps));
            }
        }
    }
}

/// short source image of a simple expression (`Foo`, `Permutations(Foo)`), as `getHumanReadableImage` would print it
fn expr_image(e: &sem::Expr) -> String {
    match &e.kind {
        EKind::Apply(Callee::Def(d), args) if args.is_empty() => d.name.to_string(),
        EKind::Apply(Callee::Decl(d), args) if args.is_empty() => d.name.to_string(),
        EKind::Apply(Callee::Def(d), args) => {
            let a: Vec<String> = args
                .iter()
                .map(|x| match x {
                    sem::Arg::Expr(x) => expr_image(x),
                    _ => "_".to_string(),
                })
                .collect();
            format!("{}({})", d.name, a.join(", "))
        }
        _ => format!("line {}, col {}", e.loc.bl, e.loc.bc),
    }
}

impl Setup {
    /// Java: `Tool.getSymmetryPerms` warning (EC.TLC_SYMMETRY_SET_TOO_SMALL): symmetry sets with fewer than two elements
    pub fn symmetry_warning(&self, nfuncs: usize, members: &HashSet<u32>) -> R<Option<String>> {
        let def = match &self.symmetry_def {
            Some(d) => d,
            None => return Ok(None),
        };
        let body = match def.body() {
            Some(b) => b,
            None => return Ok(None),
        };
        let argnodes: Vec<sem::Expr> = match &body.kind {
            EKind::Bi(_, args) => args.clone(),
            EKind::Apply(_, args) => args
                .iter()
                .filter_map(|a| match a {
                    sem::Arg::Expr(x) => Some(x.clone()),
                    _ => None,
                })
                .collect(),
            _ => vec![],
        };
        let mut offenders: Vec<String> = vec![];
        let name_of = |node: &sem::Expr| -> String {
            let image = expr_image(node);
            let alias = match image.strip_prefix("Permutations(") {
                Some(r) => r.trim_end_matches(')').to_string(),
                None => image.clone(),
            };
            self.override_rev.get(&alias).cloned().unwrap_or(alias)
        };
        if argnodes.len() >= nfuncs {
            for n in &argnodes {
                offenders.push(name_of(n));
            }
        }
        let _ = members;
        if offenders.is_empty() {
            return Ok(None);
        }
        let k = offenders.len();
        let (pl, have, anti) = if k > 1 { ("s", "have", "") } else { ("", "has", "s") };
        Ok(Some(format!(
            "The set{} {} {} been defined to be a symmetry set but contain{} less than two elements.",
            pl,
            offenders.join(", and "),
            have,
            anti
        )))
    }
}

/// Java: `SpecProcessor.processConfigPossible`: every `_POSSIBLE` predicate is tracked by a generated
/// `_Track(P, "P")` definition (state-level predicates become model constraints, action-level ones action
/// constraints) and checked after the state space has been explored by `_CheckName("P")`.
fn process_config_possible(setup: &mut Setup, root: &Rc<sem::ModuleNode>, cfg: &ModelConfig, analyze: ModuleAnalyzer) -> Result<(), SetupErr> {
    if cfg.possible.is_empty() {
        return Ok(());
    }
    let mut user: Vec<Rc<sem::OpDef>> = Vec::new();
    for name in &cfg.possible {
        match root.lookup(name) {
            None => {
                return serr(
                    ec::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
                    format!("The possible {} specified in the configuration file
is not defined in the specification.", name),
                )
            }
            Some(sem::Sym::Def(d)) => {
                if d.arity() != 0 {
                    return serr(ec::TLC_CONFIG_ID_REQUIRES_NO_ARG, format!("TLC requires possible {} not to take any argument.", name));
                }
                // https://github.com/tlaplus/tlaplus/issues/827
                if d.level.get() >= sem::Level::Temporal {
                    return serr(
                        ec::TLC_CONFIG_ID_HAS_VALUE,
                        format!("The possible of {} is equal to a temporal formula; only state- and action-level predicates are supported", name),
                    );
                }
                user.push(d);
            }
            Some(_) => return serr(ec::TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, format!("The possible {} cannot be a constant.", name)),
        }
    }
    // Java: ModuleNode.generateUnusedName: the suffix is the current time in milliseconds
    let unused = |pattern: &str| -> String {
        let mut suffix = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_millis()).unwrap_or(0);
        loop {
            let n = pattern.replace("%s", &suffix.to_string());
            if root.lookup(&n).is_none() {
                return n;
            }
            suffix += 1;
        }
    };
    let root_name = root.name.to_string();
    let mod_name = unused("_PossibleModule_%s");
    let mut ac_names = Vec::new();
    let mut ac_defs = String::new();
    let mut pc_names = Vec::new();
    let mut pc_defs = String::new();
    for name in &cfg.possible {
        let ac = unused(&format!("_PossibleAC_{}_%s", name));
        ac_defs.push_str(&format!("{} == _Track({}, \"{}\")

", ac, name, name));
        ac_names.push(ac);
    }
    for name in &cfg.possible {
        let pc = unused(&format!("_PossiblePC_{}_%s", name));
        pc_defs.push_str(&format!("{} == _CheckName(\"{}\")

", pc, name));
        pc_names.push(pc);
    }
    let src = format!("---- MODULE {} ----
EXTENDS {}, _Possible

{}{}

====", mod_name, root_name, ac_defs, pc_defs);
    let module = match analyze(&src) {
        Ok(m) => m,
        Err(e) => return serr(ec::TLC_PARSING_FAILED2, format!("_POSSIBLE: {}", e)),
    };
    let def_of = |n: &str| -> Result<Rc<sem::OpDef>, SetupErr> {
        match module.lookup(n) {
            Some(sem::Sym::Def(d)) => Ok(d),
            _ => Err(SetupErr { code: ec::TLC_PARSING_FAILED2, text: format!("_POSSIBLE: generated definition {} is missing", n) }),
        }
    };
    // state-level predicates -> model constraints, action-level ones -> action constraints
    let (mut state_c, mut action_c) = (Vec::new(), Vec::new());
    for (i, u) in user.iter().enumerate() {
        let def = def_of(&ac_names[i])?;
        // The wrapper is evaluated for every state / transition (Java never folds the generated definitions): it
        // takes the level of the predicate it tracks, which SANY does not propagate through `TLCSet(k, v) == TRUE`.
        def.level.set(sem::Level::max(def.level.get(), u.level.get()));
        let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
        let (ex, n) = setup.comp.compile_top(&e);
        let top = Top { name: ac_names[i].clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] };
        if u.level.get() <= sem::Level::State {
            state_c.push(top);
        } else {
            action_c.push(top);
        }
    }
    setup.action_constraints.extend(action_c);
    setup.constraints.extend(state_c);
    for (i, u) in user.iter().enumerate() {
        let def = def_of(&pc_names[i])?;
        let e = sem::Expr::new(EKind::Apply(Callee::Def(def.clone()), vec![]), def.loc, def.level.get());
        let (ex, n) = setup.comp.compile_top(&e);
        let loc = sem_body_loc(u);
        let text = format!("line {}, col {} to line {}, col {} of module {}", loc.bl, loc.bc, loc.el, loc.ec, u.original().module);
        setup.postconditions.push((Top { name: cfg.possible[i].clone(), ex, nslots: n, loc: def.loc, module: def.module.to_string(), bound: vec![] }, text, true));
    }
    Ok(())
}
