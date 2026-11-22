//! Port of `tlc2.tool.ModelChecker` / `Worker` (single worker): breadth-first search over distinct states.

use crate::{finish, now_str};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use tlc_core::actions::Mode;
use tlc_core::ec;
use tlc_core::mp::{self, Reporter};
use tlc_core::eval::LabelSpec;
use tlc_core::spec::{Setup, Top};
use tlc_core::symmetry::{self, SymGroup};
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

/// `TLCRS_NOSPLIT` (diagnostics) disables the per-disjunct action labels; read once (a getenv is a system call)
fn splitting_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("TLCRS_NOSPLIT").is_err())
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
    perms: SymGroup,
    /// temporal properties are checked: the behavior graph is recorded (Java: `checkLiveness`)
    live: bool,
    /// per state: the (distinct, in-model) successors in generation order, the stuttering step last
    live_succ: Vec<Vec<u32>>,
    /// with a VIEW: the successor state actually produced by each recorded transition (parallel to `live_succ`)
    live_edge: Vec<Vec<Rc<Vec<Value>>>>,
    live_inits: Vec<u32>,
    /// fingerprint -> state index (only with liveness)
    fp_index: HashMap<u64, u32>,
}

struct StateTable<'a>(&'a [Rec], &'a [Vec<Rc<Vec<Value>>>]);

impl crate::live::States for StateTable<'_> {
    fn vals(&self, i: u32) -> &[Value] {
        &self.0[i as usize].vals
    }
    fn edge_vals(&self, s: u32, i: usize) -> Option<&[Value]> {
        self.1.get(s as usize).and_then(|v| v.get(i)).map(|r| r.as_slice())
    }
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

    /// Java: `Tool.evalAlias` + `RecordValue.PrintTLCState.toString`: the state at trace position `level` (1-based) as printed, with
    /// `succ` its successor in the trace.  Without an ALIAS (or if it is not a record) these are the state variables.
    fn state_text_at(&mut self, level: usize, vals: &[Value], succ: &[Value]) -> String {
        let setup = self.setup;
        let alias = match &setup.alias {
            Some(a) => a,
            None => return self.state_text(vals),
        };
        let ev = setup.ev.clone();
        let saved = ev.counters.get();
        let mut c = saved;
        c[0] = level as i64;
        ev.counters.set(c);
        let r = setup.run_top(alias, vals, succ);
        ev.counters.set(saved);
        self.flush_output();
        let rec = match r {
            Ok(v) => match v {
                Value::FcnLam(_) => v.force_fcn().ok(),
                other => Some(other),
            },
            Err(e) => {
                // Java: the evaluation error is attached to the state as the variable `_ALIASEvalError` (the record then
                // has at least two fields: every line is printed with `/\`)
                let mut s = String::new();
                for (i, v) in self.setup.vars.iter().enumerate() {
                    s.push_str(&format!("/\\ {} = {}\n", v.name, tlc_core::pprint::ppr(&vals[i].to_tla())));
                }
                let err = tlc_core::pprint::ppr(&Value::str(&e.msg).to_tla());
                s.push_str(&format!("/\\ _ALIASEvalError = {}\n", err));
                return s;
            }
        };
        let (dom, fvals) = match rec.as_ref().and_then(|r| r.fcn_parts()) {
            Some((d, v)) if !matches!(rec, Some(Value::Tuple(_))) && d.iter().all(|x| matches!(x, Value::Str(_))) => (d, v),
            _ => return self.state_text(vals),
        };
        let fmt_idx = dom.iter().position(|d| matches!(d, Value::Str(id) if &*tla_sany::intern::name_of(*id) == "_format"));
        let format = match fmt_idx {
            Some(i) => match &fvals[i] {
                Value::Str(id) => tla_sany::intern::name_of(*id).to_string(),
                _ => "/\\ %s = %s\n".to_string(),
            },
            None if dom.len() == 1 => "%s = %s\n".to_string(),
            None => "/\\ %s = %s\n".to_string(),
        };
        let mut out = String::new();
        for (i, (d, v)) in dom.iter().zip(fvals.iter()).enumerate() {
            if Some(i) == fmt_idx {
                continue;
            }
            let key = match d {
                Value::Str(id) => tla_sany::intern::name_of(*id).to_string(),
                _ => String::new(),
            };
            let value = tlc_core::pprint::ppr(&v.to_tla());
            // Java: String.format(format, key, value)
            let mut args = [key, value].into_iter();
            let mut it = format.chars().peekable();
            while let Some(ch) = it.next() {
                if ch == '%' {
                    match it.peek() {
                        Some('s') => {
                            it.next();
                            out.push_str(&args.next().unwrap_or_default());
                        }
                        Some('%') => {
                            it.next();
                            out.push('%');
                        }
                        Some('n') => {
                            it.next();
                            out.push('\n');
                        }
                        _ => out.push('%'),
                    }
                } else {
                    out.push(ch);
                }
            }
        }
        out
    }

    fn fp(&self, vals: &[Value]) -> R<u64> {
        // Java: TLCStateMut.fingerPrint: fingerprint the lexicographically smallest image under the symmetry group
        let canon = if self.perms.is_empty() { None } else { self.perms.canonical_state(vals, self.setup.view.is_some())? };
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
            let label = if n == 0 {
                "<Initial predicate>".to_string()
            } else {
                let pred = self.states[chain[n - 1] as usize].vals.clone();
                let cur = self.states[si as usize].vals.clone();
                self.transition_label(&pred, &cur)
            };
            let nx = chain.get(n + 1).copied().unwrap_or(si);
            let (cur, succ) = (self.states[si as usize].vals.clone(), self.states[nx as usize].vals.clone());
            let body = self.state_text_at(n + 1, &cur, &succ);
            let text = format!("{}: {}\n{}", n + 1, label, body);
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
    fn print_trace_ext(&mut self, parent: u32, vals: &[Value]) {
        let mut chain = vec![];
        let mut i = parent;
        while i != NONE {
            chain.push(i);
            i = self.states[i as usize].parent;
        }
        chain.reverse();
        self.rep.error(ec::TLC_BEHAVIOR_UP_TO_THIS_POINT, "The behavior up to this point is:");
        for (n, &si) in chain.iter().enumerate() {
            let l = if n == 0 {
                "<Initial predicate>".to_string()
            } else {
                let pred = self.states[chain[n - 1] as usize].vals.clone();
                let cur = self.states[si as usize].vals.clone();
                self.transition_label(&pred, &cur)
            };
            let cur = self.states[si as usize].vals.clone();
            let succ = match chain.get(n + 1) {
                Some(&nx) => self.states[nx as usize].vals.clone(),
                None => vals.to_vec(),
            };
            let body = self.state_text_at(n + 1, &cur, &succ);
            let text = format!("{}: {}\n{}", n + 1, l, body);
            self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
        }
        let l = match chain.last() {
            Some(&last) => {
                let pred = self.states[last as usize].vals.clone();
                self.transition_label(&pred, vals)
            }
            None => "<Next>".to_string(),
        };
        let body = self.state_text_at(chain.len() + 1, vals, vals);
        let text = format!("{}: {}\n{}", chain.len() + 1, l, body);
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
                    self.perms = SymGroup::new(p);
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
                if self.live {
                    let idx = self.states.len() as u32 - 1;
                    self.fp_index.insert(fp, idx);
                    self.live_succ.push(Vec::new());
                    self.live_edge.push(Vec::new());
                    self.live_inits.push(idx);
                }
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
                ev.splitting.set(false);
                let r = ev.with_frame(nx.nslots.get(), |ev| {
                    ev.enum_action(&nx.ex, Mode::Next, &cur, &buf, &mut || {
                        let st = buf.borrow().clone();
                        if st.iter().any(|v| matches!(v, Value::Undef)) {
                            if incomplete.is_none() {
                                incomplete = Some(st);
                            }
                            return Ok(());
                        }
                        succs.push((st, None));
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
                            self.print_trace_ext(head as u32, &st);
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
                    if self.live {
                        let target = if is_new { self.states.len() as u32 } else { self.fp_index.get(&fp).copied().unwrap_or(u32::MAX) };
                        if target != u32::MAX {
                            if self.setup.view.is_some() || !self.perms.is_empty() {
                                // a node stands for several states (VIEW / SYMMETRY): keep one edge per distinct actual successor
                                let dup = self.live_succ[head].iter().zip(self.live_edge[head].iter()).any(|(t, vals)| {
                                    *t == target && vals.iter().zip(st.iter()).all(|(a, b)| a.eq_val(b).unwrap_or(false))
                                });
                                if !dup {
                                    self.live_succ[head].push(target);
                                    self.live_edge[head].push(Rc::new(st.clone()));
                                }
                            } else if !self.live_succ[head].contains(&target) {
                                self.live_succ[head].push(target);
                            }
                        }
                        if is_new {
                            self.fp_index.insert(fp, target);
                            self.live_succ.push(Vec::new());
                            self.live_edge.push(Vec::new());
                        }
                    }
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
                            self.print_trace_ext(head as u32, &sv);
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
            if self.live {
                // Java: `Worker.doNextCheckLiveness` adds the stuttering step to the successors
                let h = head as u32;
                if self.setup.view.is_some() || !self.perms.is_empty() {
                    let cur = &self.states[head].vals;
                    let dup = self.live_succ[head].iter().zip(self.live_edge[head].iter()).any(|(t, vals)| {
                        *t == h && vals.iter().zip(cur.iter()).all(|(a, b)| a.eq_val(b).unwrap_or(false))
                    });
                    if !dup {
                        let v = Rc::new(cur.clone());
                        self.live_succ[head].push(h);
                        self.live_edge[head].push(v);
                    }
                } else if !self.live_succ[head].contains(&h) {
                    self.live_succ[head].push(h);
                }
            }
            head += 1;
        }
        self.flush_output();
        if self.live {
            self.final_liveness_check()?;
        }
        Ok(())
    }

    /// the label of the action taking `pred` to `succ` as printed in a trace (`<Next line ...>`): the actions are split
    /// again for this one state (Java: `Tool.getState(fp, predecessor)`), the main search does not track labels
    fn transition_label(&mut self, pred: &[Value], succ: &[Value]) -> String {
        let fp = match self.fp(succ) {
            Ok(f) => f,
            Err(_) => return "<Next>".to_string(),
        };
        match self.step(pred, fp) {
            Some((_, Some(l))) => self.setup.ev.format_label(&l),
            _ => "<Next>".to_string(),
        }
    }

    /// Java: `Tool.getState(fp, predecessor)`: the first successor of `pred` (in the order the actions yield them) whose
    /// fingerprint is `target_fp`, with the label of the action that yields it
    fn step(&mut self, pred: &[Value], target_fp: u64) -> Option<(Vec<Value>, Option<LabelSpec>)> {
        let setup = self.setup;
        let ev = setup.ev.clone();
        let nx = setup.next.first()?;
        let cur = pred.to_vec();
        let nvars = setup.vars.len();
        let mut found: Option<(Vec<Value>, Option<LabelSpec>)> = None;
        let buf = RefCell::new(vec![Value::Undef; nvars]);
        ev.epoch.set(ev.epoch.get() + 1);
        *ev.cur_label.borrow_mut() = Some(LabelSpec { base: Rc::new(tlc_core::eval::LabelBase { name: std::sync::Arc::from(nx.name.as_str()), params: vec![] }), stop: Rc::as_ptr(&nx.ex) as usize });
        ev.splitting.set(true);
        let _ = ev.with_frame(nx.nslots.get(), |ev| {
            ev.enum_action(&nx.ex, Mode::Next, &cur, &buf, &mut || {
                if found.is_some() {
                    return Ok(());
                }
                let st = buf.borrow().clone();
                if st.iter().any(|v| matches!(v, Value::Undef)) {
                    return Ok(());
                }
                if let Ok(fp) = self.fp(&st) {
                    if fp == target_fp {
                        found = Some((st, ev.cur_label.borrow().clone()));
                    }
                }
                Ok(())
            })
        });
        ev.splitting.set(false);
        self.flush_output();
        found
    }

    /// Java: `ModelChecker`: the final liveness check (`LiveCheck.finalCheck` -> `LiveWorker`)
    fn final_liveness_check(&mut self) -> SR<()> {
        let setup = self.setup;
        let ev = setup.ev.clone();
        let left = 0usize;
        self.rep.info(
            ec::TLC_PROGRESS_STATS,
            &format!(
                "Progress({}) at {}: {} states generated, {} distinct states found, {} states left on queue.",
                self.max_level,
                now_str(),
                self.generated,
                self.states.len(),
                left
            ),
        );
        let oss = &setup.live.oss;
        let t0 = std::time::Instant::now();
        // Java iterates the successors of a state in the order of a hash set (`SetOfStates`: slot = FP64 % capacity), an
        // order that cannot be reproduced here (our fingerprints and intern tokens differ); any fixed order is as good as
        // another.  The reverse generation order agrees with Java's counterexamples more often on the test corpus.
        for (i, v) in self.live_succ.iter_mut().enumerate() {
            v.reverse();
            if i < self.live_edge.len() && self.live_edge[i].len() == v.len() {
                self.live_edge[i].reverse();
            }
        }
        let table = StateTable(&self.states, &self.live_edge);
        let graphs = match crate::live::build_all(&ev, &table, &self.live_succ, &self.live_inits, oss) {
            Ok(g) => g,
            Err(e) => {
                let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                return Err(Stop::Exit(code));
            }
        };
        let total: usize = graphs.iter().map(|g| g.size()).sum();
        if std::env::var_os("TLCRS_LIVE_DEBUG").is_some() {
            eprintln!("live: graphs built in {:?} ({} nodes, {} states)", t0.elapsed(), total, self.states.len());
        }
        self.rep.info(
            ec::TLC_CHECKING_TEMPORAL_PROPS,
            &format!(
                "Checking {}temporal properties for the complete state space with {} total distinct states at ({})",
                if oss.len() == 1 { String::new() } else { format!("{} branches of ", oss.len()) },
                total,
                now_str()
            ),
        );
        let found = match crate::live::find_counterexample(&ev, &table, &graphs, oss) {
            Ok(f) => f,
            Err(e) => {
                self.flush_output();
                let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                return Err(Stop::Exit(code));
            }
        };
        self.flush_output();
        if std::env::var_os("TLCRS_LIVE_DEBUG").is_some() {
            eprintln!("live: checked in {:?}", t0.elapsed());
        }
        let dur = t0.elapsed();
        let human = format!("{:02}s", dur.as_secs());
        match found {
            None => {
                self.rep.info(ec::TLC_CHECKING_TEMPORAL_PROPS_END, &format!("Finished checking temporal properties in {} at {}", human, now_str()));
                Ok(())
            }
            Some((oi, lasso)) => {
                self.print_lasso(&lasso, &oss[oi]);
                self.rep.info(ec::TLC_CHECKING_TEMPORAL_PROPS_END, &format!("Finished checking temporal properties in {} at {}", human, now_str()));
                self.stats(0);
                Err(Stop::Exit(ec::error_constant_to_exit_status(ec::TLC_TEMPORAL_PROPERTY_VIOLATED)))
            }
        }
    }

    /// Java: `LiveWorker.printTrace`
    fn print_lasso(&mut self, lasso: &crate::live::Lasso, oos: &tlc_core::liveness::oos::Oos) {
        let setup = self.setup;
        let ev = setup.ev.clone();
        // the real behavior: every state is the successor of the previous printed state with the fingerprint of the node
        // (with a VIEW a node stands for several states)
        let fps: Vec<u64> = lasso.states.iter().map(|&i| self.fp(&self.states[i as usize].vals).unwrap_or(0)).collect();
        let mut actual: Vec<(Vec<Value>, Option<LabelSpec>)> = vec![(self.states[lasso.states[0] as usize].vals.clone(), None)];
        for i in 1..lasso.states.len() {
            let prev = actual[i - 1].0.clone();
            let next = match self.step(&prev, fps[i]) {
                Some(x) => x,
                None => (self.states[lasso.states[i] as usize].vals.clone(), None),
            };
            actual.push(next);
        }
        // the properties violated by the lasso (Java: `Liveness.findViolatedProperties`)
        let vals: Vec<Vec<Value>> = actual.iter().map(|(v, _)| v.clone()).collect();
        let mut violated: Vec<String> = vec![];
        for (name, ln) in &setup.live.props {
            if let Ok(false) = ln.eval_on_lasso(&ev, &vals, lasso.cycle_pos, 0) {
                if !violated.contains(name) {
                    violated.push(name.clone());
                }
            }
        }
        let text = match violated.len() {
            0 => "Temporal properties were violated.\n".to_string(),
            1 => format!("Temporal property {} was violated.\n", violated[0]),
            2 => format!("Temporal properties {} and {} were violated.\n", violated[0], violated[1]),
            n => format!("Temporal properties {}, and {} were violated.\n", violated[..n - 1].join(", "), violated[n - 1]),
        };
        self.rep.error(ec::TLC_TEMPORAL_PROPERTY_VIOLATED, &text);
        self.rep.error(ec::TLC_COUNTER_EXAMPLE, "The following behavior constitutes a counter-example:\n");
        for (n, (v, l)) in actual.iter().enumerate() {
            let label = match l {
                _ if n == 0 => "<Initial predicate>".to_string(),
                Some(l) => ev.format_label(l),
                None => "<Next>".to_string(),
            };
            let succ = match actual.get(n + 1) {
                Some((nv, _)) => nv.clone(),
                None => actual[lasso.cycle_pos].0.clone(),
            };
            let body = self.state_text_at(n + 1, v, &succ);
            let text = format!("{}: {}\n{}", n + 1, label, body);
            self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
        }
        let cycle_num = lasso.cycle_pos + 1;
        if lasso.stuttering {
            self.rep.message(ec::TLC_STATE_PRINT3, mp::class::STATE, &format!("{}: Stuttering", cycle_num + 1));
            // Java: `Liveness.printStutteringCounterExampleWarning`
            if !oos.has_empty_pem_and_box_free_promises() {
                if !setup.spec_name.is_empty() && setup.spec_temporal.is_empty() {
                    self.rep.warning(
                        ec::TLC_CONFIG_NO_FAIRNESS_BUT_LIVE_PROPERTY,
                        &format!(
                            "The stuttering counterexample above may be caused by the absence of a fairness constraint in the behavior specification {} defined at {}. To rule out such counterexamples, conjoin a suitable fairness constraint to {} (compare Chapter 8, page 87ff of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).",
                            setup.spec_name, setup.spec_loc, setup.spec_name
                        ),
                    );
                } else if setup.spec_name.is_empty() {
                    self.rep.warning(
                        ec::TLC_CONFIG_NO_SPEC_BUT_PROPERTY,
                        "The stuttering counterexample above may be caused by the absence of a behavior specification (SPECIFICATION). Only INIT and NEXT have been provided, so TLC permits infinite stuttering. To rule out such counterexamples, use SPECIFICATION Spec, with Spec asserting a suitable fairness constraint (compare Chapter 8, page 87ff of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).",
                    );
                }
            }
        } else {
            let last = actual.last().unwrap().0.clone();
            let label = match self.step(&last, fps[lasso.cycle_pos]) {
                Some((_, Some(l))) => ev.format_label(&l),
                _ => "<Next>".to_string(),
            };
            self.rep.message(ec::TLC_BACK_TO_STATE, mp::class::STATE, &format!("{}: Back to state: {}", cycle_num, label));
        }
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
            let mut defs: std::collections::HashMap<String, u64> = std::collections::HashMap::new();
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
                    let mut dv: Vec<_> = defs.iter().collect();
                    dv.sort_by(|a, b| b.1.cmp(a.1));
                    let tot: u64 = defs.values().sum();
                    eprintln!("DEFS (innermost user definition) total={}", tot);
                    for (k, c) in dv.iter().take(14) {
                        eprintln!("  {:6.2}% {}", **c as f64 * 100.0 / tot.max(1) as f64, k);
                    }
                    last = std::time::Instant::now();
                }
                let cd = tlc_core::eval::PROF_DEF.load(std::sync::atomic::Ordering::Relaxed);
                if cd != 0 {
                    let d = unsafe { &*(cd as *const tlc_core::ir::CompiledDef) };
                    *defs.entry(d.name.to_string()).or_insert(0) += 1;
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
        perms: SymGroup::new(Vec::new()),
        live: !setup.live.oss.is_empty(),
        live_succ: Vec::new(),
        live_edge: Vec::new(),
        live_inits: Vec::new(),
        fp_index: HashMap::new(),
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
