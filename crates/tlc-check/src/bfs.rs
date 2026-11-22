//! Port of `tlc2.tool.ModelChecker` / `Worker` (single worker): breadth-first search over distinct states.

use crate::{finish, now_str};
use std::cell::RefCell;
use std::rc::Rc;
use tlc_core::actions::Mode;
use tlc_core::ec;
use tlc_core::mp::{self, Reporter};
use tlc_core::eval::LabelSpec;
use tlc_core::spec::{Setup, Top};
use tlc_core::symmetry::{self, MvPerm};
use tlc_core::value::*;
use tlc_core::TlcOptions;

/// open-addressing set of 64-bit fingerprints (0 is stored as 1)
struct FpSet {
    tab: Vec<u64>,
    mask: usize,
    len: usize,
}

impl FpSet {
    fn new() -> FpSet {
        FpSet { tab: vec![0; 1 << 16], mask: (1 << 16) - 1, len: 0 }
    }
    /// returns true if the fingerprint was not yet present
    fn insert(&mut self, fp: u64) -> bool {
        let fp = if fp == 0 { 1 } else { fp };
        if self.len * 2 >= self.tab.len() {
            self.grow();
        }
        let mut i = (fp as usize) & self.mask;
        loop {
            let v = self.tab[i];
            if v == 0 {
                self.tab[i] = fp;
                self.len += 1;
                return true;
            }
            if v == fp {
                return false;
            }
            i = (i + 1) & self.mask;
        }
    }
    fn len(&self) -> usize {
        self.len
    }
    fn grow(&mut self) {
        let old = std::mem::take(&mut self.tab);
        self.tab = vec![0; old.len() * 2];
        self.mask = self.tab.len() - 1;
        self.len = 0;
        for v in old {
            if v != 0 {
                self.insert(v);
            }
        }
    }
}

struct Rec {
    vals: Vec<Value>,
    parent: u32,
    label: Option<LabelSpec>,
    level: u32,
}

const NONE: u32 = u32::MAX;

fn java_round(x: f64) -> i64 {
    (x + 0.5).floor() as i64
}

#[cfg(feature = "prof")]
thread_local! {
    static PROF: std::cell::RefCell<[u128; 8]> = std::cell::RefCell::new([0; 8]);
}
#[cfg(feature = "prof")]
fn prof_phase_on(name: &str) {
    if let Ok(p) = std::env::var("TLCRS_PROF_PHASE") {
        tlc_core::eval::PROF_ON.store(p == name, std::sync::atomic::Ordering::Relaxed);
    }
}
#[cfg(feature = "prof")]
fn prof_phase_off() {
    if std::env::var("TLCRS_PROF_PHASE").is_ok() {
        tlc_core::eval::PROF_ON.store(false, std::sync::atomic::Ordering::Relaxed);
    }
}
#[cfg(feature = "prof")]
fn prof_now() -> std::time::Instant {
    std::time::Instant::now()
}
#[cfg(feature = "prof")]
fn prof_add(i: usize, t: std::time::Instant) {
    PROF.with(|p| p.borrow_mut()[i] += t.elapsed().as_nanos());
}
#[cfg(not(feature = "prof"))]
fn prof_phase_on(_name: &str) {}
#[cfg(not(feature = "prof"))]
fn prof_phase_off() {}
#[cfg(not(feature = "prof"))]
fn prof_now() {}
#[cfg(not(feature = "prof"))]
fn prof_add(_i: usize, _t: ()) {}

struct Checker<'a> {
    setup: &'a Setup,
    rep: &'a mut Reporter,
    states: Vec<Rec>,
    fps: FpSet,
    generated: u64,
    start: std::time::Instant,
    opts: &'a TlcOptions,
    max_level: u32,
    /// per-state out-degrees (for the 2268 statistics)
    outdeg: Vec<u32>,
    /// symmetry group (Java: `Tool.getSymmetryPerms`); empty when there is no SYMMETRY
    perms: Vec<MvPerm>,
}

enum Stop {
    /// an error was reported; exit with this status
    Exit(i32),
}

type SR<T> = Result<T, Stop>;

impl<'a> Checker<'a> {
    /// publish the counters TLCGet reads
    fn set_counters(&self, level: i64, queue: i64) {
        let ev = &self.setup.ev;
        let secs = self.start.elapsed().as_secs() as i64;
        ev.counters.set([level, self.generated as i64, self.fps.len() as i64, queue, self.max_level as i64, secs]);
    }

    fn flush_output(&mut self) {
        let lines: Vec<String> = self.setup.ev.out.borrow_mut().drain(..).collect();
        for l in lines {
            self.rep.raw(&l);
        }
    }

    /// Java: TLCStateMut.toString: `/\ var = ppr(value)` lines (a lone variable prints without the `/\`)
    fn state_text(&self, vals: &[Value]) -> String {
        let mut s = String::new();
        let single = self.setup.vars.len() == 1;
        for (i, v) in self.setup.vars.iter().enumerate() {
            let val = tlc_core::pprint::ppr(&vals[i].to_tla());
            if single {
                s.push_str(&format!("{} = {}\n", v.name, val));
            } else {
                s.push_str(&format!("/\\ {} = {}\n", v.name, val));
            }
        }
        s
    }

    fn fp(&self, vals: &[Value]) -> R<u64> {
        // Java: TLCStateMut.fingerPrint: fingerprint the lexicographically smallest image under the symmetry group
        let canon = if self.perms.is_empty() { None } else { symmetry::canonical(vals, &self.perms)? };
        let vals: &[Value] = match &canon {
            Some(c) => c,
            None => vals,
        };
        let mut h = Hasher::new();
        if let Some(view) = &self.setup.view {
            let v = self.setup.run_top(view, vals, &self.setup.ev.empty())?;
            v.hash_into(&mut h)?;
        } else {
            for v in vals {
                v.hash_into(&mut h)?;
            }
        }
        Ok(h.finish())
    }

    fn report_err(&mut self, e: &TlcErr, default_exit: i32) -> i32 {
        self.flush_output();
        if e.not_ported {
            self.rep.error(mp::NOT_PORTED, &e.msg);
            return 199;
        }
        self.rep.error(e.code, &e.msg);
        match e.code {
            ec::TLC_VALUE_ASSERT_FAILED => ec::exit_status::VIOLATION_ASSERT,
            ec::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM => ec::exit_status::ERROR_CONFIG_PARSE,
            ec::SYSTEM_STACK_OVERFLOW => ec::exit_status::ERROR,
            _ => default_exit,
        }
    }

    fn in_model(&mut self, vals: &[Value]) -> R<bool> {
        for c in &self.setup.constraints {
            if !self.setup.run_top(c, vals, &self.setup.ev.empty())?.as_bool()? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn action_ok(&mut self, cur: &[Value], succ: &[Value]) -> R<bool> {
        for c in &self.setup.action_constraints {
            if !self.setup.run_top(c, cur, succ)?.as_bool()? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn print_trace(&mut self, idx: u32) {
        let mut chain = vec![];
        let mut i = idx;
        while i != NONE {
            chain.push(i);
            i = self.states[i as usize].parent;
        }
        chain.reverse();
        self.rep.error(ec::TLC_BEHAVIOR_UP_TO_THIS_POINT, "The behavior up to this point is:");
        for (n, &si) in chain.iter().enumerate() {
            let label = match &self.states[si as usize].label {
                Some(l) => self.setup.ev.format_label(l),
                None => "<Initial predicate>".to_string(),
            };
            let text = format!("{}: {}\n{}", n + 1, label, self.state_text(&self.states[si as usize].vals));
            self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
        }
    }

    /// check the invariants on a state; `Some(name)` if one is violated
    fn check_invariants(&mut self, vals: &[Value]) -> Result<Option<String>, (Box<TlcErr>, String)> {
        for inv in &self.setup.invariants {
            match self.setup.run_top(inv, vals, &self.setup.ev.empty()) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => return Ok(Some(inv.name.clone())),
                Ok(other) => {
                    return Err((
                        Box::new(TlcErr {
                            code: ec::GENERAL,
                            msg: format!("The invariant {} evaluated to the non-boolean value\n{}", inv.name, other.to_tla()),
                            not_ported: false,
                            trail: vec![],
                        }),
                        inv.name.clone(),
                    ))
                }
                Err(e) => return Err((e, inv.name.clone())),
            }
        }
        Ok(None)
    }

    /// Java: `Tool.getImpliedInits` checks; `Some(name)` for the first violated implied initial predicate
    fn check_implied_inits(&mut self, vals: &[Value]) -> Result<Option<String>, (Box<TlcErr>, String)> {
        for p in &self.setup.implied_inits {
            match self.setup.run_top(p, vals, &self.setup.ev.empty()) {
                Ok(Value::Bool(true)) => {}
                Ok(_) => return Ok(Some(p.name.clone())),
                Err(e) => return Err((e, p.name.clone())),
            }
        }
        Ok(None)
    }

    /// Java: `Tool.getImpliedActions` checks on the step `cur -> succ`
    fn check_implied_actions(&mut self, cur: &[Value], succ: &[Value]) -> Result<Option<String>, (Box<TlcErr>, String)> {
        for p in &self.setup.implied_actions {
            match self.setup.run_top(p, cur, succ) {
                Ok(Value::Bool(true)) => {}
                Ok(_) => return Ok(Some(p.name.clone())),
                Err(e) => return Err((e, p.name.clone())),
            }
        }
        Ok(None)
    }

    /// the behavior leading to `parent`, followed by the state `vals` reached by `label`
    fn print_trace_ext(&mut self, parent: u32, vals: &[Value], label: &Option<LabelSpec>) {
        let mut chain = vec![];
        let mut i = parent;
        while i != NONE {
            chain.push(i);
            i = self.states[i as usize].parent;
        }
        chain.reverse();
        self.rep.error(ec::TLC_BEHAVIOR_UP_TO_THIS_POINT, "The behavior up to this point is:");
        for (n, &si) in chain.iter().enumerate() {
            let l = match &self.states[si as usize].label {
                Some(l) => self.setup.ev.format_label(l),
                None => "<Initial predicate>".to_string(),
            };
            let text = format!("{}: {}\n{}", n + 1, l, self.state_text(&self.states[si as usize].vals));
            self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
        }
        let l = match label {
            Some(l) => self.setup.ev.format_label(l),
            None => "<Next>".to_string(),
        };
        let text = format!("{}: {}\n{}", chain.len() + 1, l, self.state_text(vals));
        self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
    }

    fn stats(&mut self, left: usize) {
        let dist = self.states.len();
        self.rep.info(
            ec::TLC_PROGRESS_STATS,
            &format!(
                "Progress({}) at {}: {} states generated, {} distinct states found, {} states left on queue.",
                self.max_level,
                now_str(),
                self.generated,
                dist,
                left
            ),
        );
        self.rep.info(
            ec::TLC_STATS,
            &format!("{} states generated, {} distinct states found, {} states left on queue.", self.generated, dist, left),
        );
        self.rep.info(ec::TLC_SEARCH_DEPTH, &format!("The depth of the complete state graph search is {}.", self.max_level));
    }

    fn outdegree_stats(&mut self) {
        if self.outdeg.is_empty() {
            return;
        }
        // Java: FixedSizedBucketStatistics(32): samples above 31 go to the overflow bucket
        let mut v: Vec<u32> = self.outdeg.iter().map(|&x| x.min(31)).collect();
        v.sort_unstable();
        let n = v.len();
        let sum: u64 = v.iter().map(|&x| x as u64).sum();
        let mean = sum as f64 / n as f64;
        let pos = ((n as f64) * 0.95) as usize;
        let p95 = v[pos.min(n - 1)];
        self.rep.info(
            ec::TLC_STATE_GRAPH_OUTDEGREE,
            &format!(
                "The average outdegree of the complete state graph is {} (minimum is {}, the maximum {} and the 95th percentile is {}).",
                java_round(mean),
                v[0],
                v[n - 1],
                p95
            ),
        );
    }

    fn run(&mut self) -> SR<()> {
        let setup = self.setup;
        let ev = setup.ev.clone();
        ev.warn.set(!self.opts.no_warning);
        {
            let mut st = ev.stats.borrow_mut();
            let seed = self.opts.seed.to_string();
            st.insert(
                "config".to_string(),
                Value::record(vec![
                    (tla_sany::intern::intern("mode"), Value::str("bfs")),
                    (tla_sany::intern::intern("deadlock"), Value::Bool(self.opts.check_deadlock && setup.check_deadlock)),
                    (tla_sany::intern::intern("worker"), Value::Int(self.opts.workers as i32)),
                    (tla_sany::intern::intern("seed"), Value::str(&seed)),
                    (tla_sany::intern::intern("fingerprint"), Value::str(&self.opts.fp_index.to_string())),
                    (tla_sany::intern::intern("install"), Value::str("tlc-rs")),
                ]),
            );
        }
        // ---- symmetry (Java: Tool.getSymmetryPerms, called when the first state is created)
        if let Some(top) = &setup.symmetry {
            let r = setup.run_top(top, &ev.empty(), &ev.empty()).and_then(|v| {
                if v.is_set_like() {
                    let nf = v.enumerate()?.len();
                    symmetry::permutation_subgroup_members(&v).map(|(p, m)| (p, m, nf))
                } else {
                    fail("The symmetry operator must specify a set of functions.")
                }
            });
            match r {
                Ok((p, members, nf)) => {
                    if let Ok(Some(w)) = setup.symmetry_warning(nf, &members) {
                        self.rep.warning(ec::TLC_SYMMETRY_SET_TOO_SMALL, &w);
                    }
                    self.perms = p;
                }
                Err(e) => {
                    let code = self.report_err(&e, ec::exit_status::ERROR);
                    return Err(Stop::Exit(code));
                }
            }
            // Java: AbstractChecker: symmetry together with temporal properties is dangerous
            if !setup.properties.is_empty() {
                self.rep.warning(ec::TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY, "Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss violations of the stated liveness properties. Please check liveness without symmetry defined.");
            }
        }
        // ---- assumptions
        for (top, desc) in &setup.assumes {
            match setup.run_top(top, &ev.empty(), &ev.empty()) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    self.flush_output();
                    self.rep.error(ec::TLC_ASSUMPTION_FALSE, &format!("Assumption {} is false.", desc));
                    return Err(Stop::Exit(ec::exit_status::VIOLATION_ASSUMPTION));
                }
                Ok(other) => {
                    self.flush_output();
                    self.rep.error(
                        ec::TLC_ASSUMPTION_EVALUATION_ERROR,
                        &format!("Evaluating assumption {} failed.\nThe assumption evaluated to the non-boolean value\n{}", desc, other.to_tla()),
                    );
                    return Err(Stop::Exit(ec::exit_status::VIOLATION_ASSUMPTION));
                }
                Err(e) => {
                    if e.not_ported {
                        self.flush_output();
                        self.rep.error(mp::NOT_PORTED, &e.msg);
                        return Err(Stop::Exit(199));
                    }
                    self.flush_output();
                    self.rep.error(ec::TLC_ASSUMPTION_EVALUATION_ERROR, &format!("Evaluating assumption {} failed.\n{}", desc, e.msg));
                    return Err(Stop::Exit(ec::exit_status::VIOLATION_ASSUMPTION));
                }
            }
        }
        // ---- initial states
        self.flush_output();
        self.rep.info(ec::TLC_COMPUTING_INIT, "Computing initial states...");
        let nvars = setup.vars.len();
        let mut init_generated = 0u64;
        let mut inits: Vec<Vec<Value>> = vec![];
        for top in &setup.init {
            let buf = RefCell::new(vec![Value::Undef; nvars]);
            let mut produced: Vec<Vec<Value>> = vec![];
            let r = ev.with_frame(top.nslots.get(), |ev| {
                ev.epoch.set(ev.epoch.get() + 1);
                ev.enum_action(&top.ex, Mode::Init, &ev.empty(), &buf, &mut || {
                    let st = buf.borrow().clone();
                    produced.push(st);
                    Ok(())
                })
            });
            if let Err(e) = r {
                let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                return Err(Stop::Exit(code));
            }
            for st in produced {
                if let Some(i) = st.iter().position(|v| matches!(v, Value::Undef)) {
                    self.flush_output();
                    let mut txt = String::new();
                    for (j, v) in setup.vars.iter().enumerate() {
                        if matches!(st[j], Value::Undef) {
                            txt.push_str(&format!("/\\ {} = undefined\n", v.name));
                        } else {
                            txt.push_str(&format!("/\\ {} = {}\n", v.name, st[j].to_tla()));
                        }
                    }
                    let _ = i;
                    self.rep.error(
                        ec::TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL,
                        &format!("State is not completely specified by the initial predicate:\n{}", txt),
                    );
                    return Err(Stop::Exit(ec::error_constant_to_exit_status(ec::TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL)));
                }
                init_generated += 1;
                inits.push(st);
            }
        }
        self.flush_output();
        let mut distinct_init = 0u64;
        let mut first_violation: Option<(usize, String, bool)> = None;
        for st in inits {
            // constraints are applied to the initial states as well
            match self.in_model(&st) {
                Ok(true) => {}
                Ok(false) => continue,
                Err(e) => {
                    let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                    return Err(Stop::Exit(code));
                }
            }
            let fp = match self.fp(&st) {
                Ok(f) => f,
                Err(e) => {
                    let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                    return Err(Stop::Exit(code));
                }
            };
            if self.fps.insert(fp) {
                distinct_init += 1;
                self.states.push(Rec { vals: st, parent: NONE, label: None, level: 1 });
                if first_violation.is_none() {
                    let idx = self.states.len() - 1;
                    let vals = self.states[idx].vals.clone();
                    match self.check_invariants(&vals) {
                        Ok(None) => match self.check_implied_inits(&vals) {
                            Ok(None) => {}
                            Ok(Some(name)) => first_violation = Some((idx, name, true)),
                            Err((e, _name)) => {
                                self.flush_output();
                                let code = self.report_err(&e, ec::exit_status::FAILURE_SAFETY_EVAL);
                                return Err(Stop::Exit(if e.code == ec::TLC_VALUE_ASSERT_FAILED { code } else { ec::exit_status::FAILURE_SAFETY_EVAL }));
                            }
                        },
                        Ok(Some(name)) => first_violation = Some((idx, name, false)),
                        Err((e, name)) => {
                            self.flush_output();
                            self.rep.error(ec::TLC_INVARIANT_EVALUATION_FAILED, &format!("Evaluating invariant {} failed.", name));
                            let code = self.report_err(&e, ec::exit_status::FAILURE_SAFETY_EVAL);
                            return Err(Stop::Exit(if e.code == ec::TLC_VALUE_ASSERT_FAILED { code } else { ec::exit_status::FAILURE_SAFETY_EVAL }));
                        }
                    }
                }
            }
        }
        self.generated = init_generated;
        self.max_level = if self.states.is_empty() { 0 } else { 1 };
        let plural = |n: u64| if n == 1 { "" } else { "s" };
        if init_generated == distinct_init {
            self.rep.info(
                ec::TLC_INIT_GENERATED1,
                &format!("Finished computing initial states: {} distinct state{} generated at {}.", distinct_init, plural(distinct_init), now_str()),
            );
        } else {
            self.rep.info(
                ec::TLC_INIT_GENERATED2,
                &format!(
                    "Finished computing initial states: {} state{} generated, with {} of them distinct at {}.",
                    init_generated,
                    plural(init_generated),
                    distinct_init,
                    now_str()
                ),
            );
        }
        if let Some((idx, name, is_prop)) = first_violation {
            let st = self.state_text(&self.states[idx].vals);
            if is_prop {
                self.rep.error(ec::TLC_PROPERTY_VIOLATED_INITIAL, &format!("Property {} is violated by the initial state:
{}", name, st));
            } else {
                self.rep.error(ec::TLC_INVARIANT_VIOLATED_INITIAL, &format!("Invariant {} is violated by the initial state:
{}", name, st));
            }
            self.stats(self.states.len());
            return Err(Stop::Exit(ec::error_constant_to_exit_status(if is_prop { ec::TLC_PROPERTY_VIOLATED_INITIAL } else { ec::TLC_INVARIANT_VIOLATED_INITIAL })));
        }
        // ---- breadth-first search
        let next = setup.next.first();
        let mut head = 0usize;
        while head < self.states.len() {
            let cur = self.states[head].vals.clone();
            ev.epoch.set(ev.epoch.get() + 1);
            let cur_level = self.states[head].level;
            self.set_counters(cur_level as i64, (self.states.len() - head - 1) as i64);
            let mut succs: Vec<(Vec<Value>, Option<LabelSpec>)> = vec![];
            let mut incomplete: Option<Vec<Value>> = None;
            prof_phase_on("enum");
            let t_enum = prof_now();
            if let Some(nx) = next {
                let buf = RefCell::new(vec![Value::Undef; nvars]);
                *ev.cur_label.borrow_mut() = Some(LabelSpec { base: Rc::new(tlc_core::eval::LabelBase { name: std::sync::Arc::from(nx.name.as_str()), params: vec![] }), stop: Rc::as_ptr(&nx.ex) as usize });
                ev.splitting.set(std::env::var("TLCRS_NOSPLIT").is_err());
                let r = ev.with_frame(nx.nslots.get(), |ev| {
                    ev.enum_action(&nx.ex, Mode::Next, &cur, &buf, &mut || {
                        let st = buf.borrow().clone();
                        if st.iter().any(|v| matches!(v, Value::Undef)) {
                            if incomplete.is_none() {
                                incomplete = Some(st);
                            }
                            return Ok(());
                        }
                        succs.push((st, ev.cur_label.borrow().clone()));
                        Ok(())
                    })
                });
                if let Err(e) = r {
                    self.flush_output();
                    let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                    if !e.not_ported {
                        self.print_trace(head as u32);
                    }
                    return Err(Stop::Exit(code));
                }
            }
            prof_phase_off();
            prof_add(0, t_enum);
            self.flush_output();
            if let Some(st) = incomplete {
                let names: Vec<String> =
                    setup.vars.iter().enumerate().filter(|(i, _)| matches!(st[*i], Value::Undef)).map(|(_, v)| v.name.to_string()).collect();
                let text = format!(
                    "Successor state is not completely specified by action {} of the next-state relation. The following variable{} not defined: {}.\n",
                    next.map(|n| n.name.clone()).unwrap_or_default(),
                    if names.len() == 1 { " is" } else { "s are" },
                    names.join(", ")
                );
                self.rep.error(ec::TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT, &text);
                self.print_trace(head as u32);
                return Err(Stop::Exit(ec::exit_status::FAILURE_SPEC_EVAL));
            }
            let nsucc = succs.len();
            let mut unseen_count: u32 = 0;
            let mut any_in_model = false;
            if nsucc == 0 && self.opts.check_deadlock && setup.check_deadlock {
                self.rep.error(ec::TLC_DEADLOCK_REACHED, "Deadlock reached.");
                self.print_trace(head as u32);
                self.generated += 0;
                self.stats(self.states.len() - head - 1);
                return Err(Stop::Exit(ec::exit_status::VIOLATION_DEADLOCK));
            }
            for (st, label) in succs {
                self.generated += 1;
                self.set_counters(cur_level as i64 + 1, (self.states.len() - head - 1) as i64);
                prof_phase_on("constraint");
                let t_c = prof_now();
                let ok = match self.in_model(&st).and_then(|m| if m { self.action_ok(&cur, &st) } else { Ok(false) }) {
                    Ok(b) => b,
                    Err(e) => {
                        let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                        self.print_trace(head as u32);
                        return Err(Stop::Exit(code));
                    }
                };
                prof_phase_off();
                prof_add(1, t_c);
                let mut just_pushed = false;
                let implied_vals = if self.setup.implied_actions.is_empty() { None } else { Some((st.clone(), label.clone())) };
                if !ok && !self.setup.invariants.is_empty() {
                    // Java: a successor outside the model is not stored but is `unseen`: its invariants are still checked
                    let inv_r = self.check_invariants(&st);
                    match inv_r {
                        Ok(None) => {}
                        Ok(Some(name)) => {
                            self.flush_output();
                            self.rep.error(ec::TLC_INVARIANT_VIOLATED_BEHAVIOR, &format!("Invariant {} is violated.", name));
                            self.print_trace_ext(head as u32, &st, &label);
                            let left = self.states.len() - head - 1;
                            self.stats(left);
                            if !self.opts.continue_after_error {
                                return Err(Stop::Exit(ec::exit_status::VIOLATION_SAFETY));
                            }
                        }
                        Err((e, name)) => {
                            self.flush_output();
                            self.rep.error(ec::TLC_INVARIANT_EVALUATION_FAILED, &format!("Evaluating invariant {} failed.", name));
                            let code = self.report_err(&e, ec::exit_status::FAILURE_SAFETY_EVAL);
                            self.print_trace(head as u32);
                            return Err(Stop::Exit(if e.code == ec::TLC_VALUE_ASSERT_FAILED { code } else { ec::exit_status::FAILURE_SAFETY_EVAL }));
                        }
                    }
                }
                if ok {
                    any_in_model = true;
                    let t_f = prof_now();
                    let fp = match self.fp(&st) {
                        Ok(f) => f,
                        Err(e) => {
                            let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                            return Err(Stop::Exit(code));
                        }
                    };
                    prof_add(2, t_f);
                    let t_s = prof_now();
                    let is_new = self.fps.insert(fp);
                    prof_add(3, t_s);
                    if is_new {
                        unseen_count += 1;
                        let level = cur_level + 1;
                        self.states.push(Rec { vals: st, parent: head as u32, label, level });
                        just_pushed = true;
                        if level > self.max_level {
                            self.max_level = level;
                        }
                        let idx = self.states.len() - 1;
                        let vals = self.states[idx].vals.clone();
                        let t_i = prof_now();
                        prof_phase_on("inv");
                        let inv_r = self.check_invariants(&vals);
                        prof_phase_off();
                        prof_add(4, t_i);
                        match inv_r {
                            Ok(None) => {}
                            Ok(Some(name)) => {
                                self.flush_output();
                                self.rep.error(ec::TLC_INVARIANT_VIOLATED_BEHAVIOR, &format!("Invariant {} is violated.", name));
                                self.print_trace(idx as u32);
                                // Java enqueues a successor only after its invariants hold: the violating state is not queued
                                let left = self.states.len() - head - 2;
                                self.stats(left);
                                if self.opts.continue_after_error {
                                    continue;
                                }
                                return Err(Stop::Exit(ec::exit_status::VIOLATION_SAFETY));
                            }
                            Err((e, name)) => {
                                self.flush_output();
                                self.rep.error(ec::TLC_INVARIANT_EVALUATION_FAILED, &format!("Evaluating invariant {} failed.", name));
                                let code = self.report_err(&e, ec::exit_status::FAILURE_SAFETY_EVAL);
                                self.print_trace(idx as u32);
                                return Err(Stop::Exit(if e.code == ec::TLC_VALUE_ASSERT_FAILED { code } else { ec::exit_status::FAILURE_SAFETY_EVAL }));
                            }
                        }
                    }
                }
                // Java: doNextCheckImplied: action properties are checked on every step, seen or not
                if let Some((sv, lb)) = implied_vals {
                    match self.check_implied_actions(&cur, &sv) {
                        Ok(None) => {}
                        Ok(Some(name)) => {
                            self.flush_output();
                            self.rep.error(ec::TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, &format!("Action property {} is violated.", name));
                            self.print_trace_ext(head as u32, &sv, &lb);
                            let left = self.states.len() - head - 1 - usize::from(just_pushed);
                            self.stats(left);
                            return Err(Stop::Exit(ec::error_constant_to_exit_status(ec::TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR)));
                        }
                        Err((e, name)) => {
                            self.flush_output();
                            self.rep.error(ec::TLC_ACTION_PROPERTY_EVALUATION_FAILED, &format!("Evaluating action property {} failed.", name));
                            let code = self.report_err(&e, ec::exit_status::FAILURE_SAFETY_EVAL);
                            self.print_trace(head as u32);
                            return Err(Stop::Exit(code));
                        }
                    }
                }
            }
            let _ = any_in_model;
            self.outdeg.push(unseen_count);
            head += 1;
        }
        self.flush_output();
        Ok(())
    }
}

#[cfg(feature = "prof")]
type Sampler = Option<(std::sync::Arc<std::sync::atomic::AtomicBool>, std::thread::JoinHandle<()>)>;

#[cfg(feature = "prof")]
fn start_sampler() -> Sampler {
    if std::env::var("TLCRS_PROF").is_ok() {
        tlc_core::eval::PROF_ON.store(true, std::sync::atomic::Ordering::Relaxed);
        let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let stop2 = stop.clone();
        let h = std::thread::spawn(move || {
            let mut hist: std::collections::HashMap<usize, (u64, String)> = std::collections::HashMap::new();
            let t0 = std::time::Instant::now();
            let mut last = std::time::Instant::now();
            let mut report = |hist: &std::collections::HashMap<usize, (u64, String)>| {
                let mut by_kind: std::collections::HashMap<String, u64> = std::collections::HashMap::new();
                let mut total = 0u64;
                for (_, (c, k)) in hist.iter() { *by_kind.entry(k.clone()).or_insert(0) += *c; total += *c; }
                let mut v: Vec<_> = by_kind.into_iter().collect();
                v.sort_by(|a, b| b.1.cmp(&a.1));
                eprintln!("SAMPLES total={} at {}s", total, t0.elapsed().as_secs());
                for (k, c) in v.iter().take(25) { eprintln!("  {:6.2}% {}", *c as f64 * 100.0 / total.max(1) as f64, k); }
            };
            while !stop2.load(std::sync::atomic::Ordering::Relaxed) {
                if last.elapsed().as_secs() >= 20 {
                    report(&hist);
                    last = std::time::Instant::now();
                }
                let cur = tlc_core::eval::PROF_CUR.load(std::sync::atomic::Ordering::Relaxed);
                if cur != 0 {
                    let e = hist.entry(cur).or_insert_with(|| {
                        let node = unsafe { &*(cur as *const tlc_core::ir::Node) };
                        (0, tlc_core::eval::node_kind(node))
                    });
                    e.0 += 1;
                }
                for _ in 0..200 { std::hint::spin_loop(); }
            }
            let mut by_kind: std::collections::HashMap<String, u64> = std::collections::HashMap::new();
            let mut total = 0u64;
            for (_, (c, k)) in hist.iter() { *by_kind.entry(k.clone()).or_insert(0) += *c; total += *c; }
            let mut v: Vec<_> = by_kind.into_iter().collect();
            v.sort_by(|a, b| b.1.cmp(&a.1));
            eprintln!("SAMPLES total={}", total);
            for (k, c) in v.iter().take(30) { eprintln!("  {:6.2}% {}", *c as f64 * 100.0 / total as f64, k); }
        });
        Some((stop, h))
    } else { None }
}

#[cfg(feature = "prof")]
fn stop_sampler(s: Sampler) {
    if let Some((stop, h)) = s {
        stop.store(true, std::sync::atomic::Ordering::Relaxed);
        let _ = h.join();
    }
}


pub fn model_check(setup: &Rc<Setup>, opts: &TlcOptions, rep: &mut Reporter, start: std::time::Instant) -> i32 {
    let mut ck = Checker {
        setup,
        rep,
        states: Vec::new(),
        fps: FpSet::new(),
        generated: 0,
        start,
        opts,
        max_level: 0,
        outdeg: Vec::new(),
        perms: Vec::new(),
    };
    #[cfg(feature = "prof")]
    let sampler = start_sampler();
    let r = ck.run();
    #[cfg(feature = "prof")]
    stop_sampler(sampler);
    #[cfg(feature = "prof")]
    if std::env::var("TLCRS_PROF").is_ok() {
        PROF.with(|p| {
            let p = p.borrow();
            eprintln!("PROF enum={}ms constraint={}ms fp={}ms fpset={}ms inv={}ms", p[0] / 1_000_000, p[1] / 1_000_000, p[2] / 1_000_000, p[3] / 1_000_000, p[4] / 1_000_000);
        });
    }
    match r {
        Ok(()) => {
            // POSTCONDITION is parsed but not evaluated yet (needs the `_POSSIBLE` named registers; see loop/NOTES.md)
            ck.rep.info(
                ec::TLC_SUCCESS,
                "Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = 0.0",
            );
            ck.stats(0);
            ck.outdegree_stats();
            finish(ck.rep, start, 0)
        }
        Err(Stop::Exit(code)) => {
            if code != 199 {
                // statistics were printed at the point of the violation
            }
            finish(ck.rep, start, code)
        }
    }
}
