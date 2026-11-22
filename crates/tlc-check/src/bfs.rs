//! Port of `tlc2.tool.ModelChecker` / `Worker` (single worker): breadth-first search over distinct states.

use crate::{finish, now_str};
use std::cell::RefCell;
use std::rc::Rc;
use tlc_core::actions::Mode;
use tlc_core::ec;
use tlc_core::mp::{self, Reporter};
use tlc_core::spec::{Setup, Top};
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
    label: Option<Rc<str>>,
    level: u32,
}

const NONE: u32 = u32::MAX;

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
}

enum Stop {
    /// an error was reported; exit with this status
    Exit(i32),
}

type SR<T> = Result<T, Stop>;

impl<'a> Checker<'a> {
    fn flush_output(&mut self) {
        let lines: Vec<String> = self.setup.ev.out.borrow_mut().drain(..).collect();
        for l in lines {
            self.rep.raw(&l);
        }
    }

    fn state_text(&self, vals: &[Value]) -> String {
        let mut s = String::new();
        for (i, v) in self.setup.vars.iter().enumerate() {
            s.push_str(&format!("/\\ {} = {}\n", v.name, vals[i].to_tla()));
        }
        s
    }

    fn fp(&self, vals: &[Value]) -> R<u64> {
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
                Some(l) => l.to_string(),
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
        let mut v = self.outdeg.clone();
        v.sort_unstable();
        let n = v.len();
        let sum: u64 = v.iter().map(|&x| x as u64).sum();
        let avg = (sum as f64 / n as f64).round() as u64;
        let p95 = v[((n as f64) * 0.95).ceil() as usize - 1usize.min(n)].max(v[(n - 1) * 95 / 100]);
        self.rep.info(
            ec::TLC_STATE_GRAPH_OUTDEGREE,
            &format!(
                "The average outdegree of the complete state graph is {} (minimum is {}, the maximum {} and the 95th percentile is {}).",
                avg,
                v[0],
                v[n - 1],
                p95
            ),
        );
    }

    fn run(&mut self) -> SR<()> {
        let setup = self.setup;
        let ev = setup.ev.clone();
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
        self.rep.info(ec::TLC_COMPUTING_INIT, "Computing initial states...");
        self.flush_output();
        let nvars = setup.vars.len();
        let mut init_generated = 0u64;
        let mut inits: Vec<Vec<Value>> = vec![];
        for top in &setup.init {
            let buf = RefCell::new(vec![Value::Undef; nvars]);
            let mut produced: Vec<Vec<Value>> = vec![];
            let r = ev.with_frame(top.nslots.get(), |ev| {
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
        let mut first_violation: Option<(usize, String)> = None;
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
                        Ok(None) => {}
                        Ok(Some(name)) => first_violation = Some((idx, name)),
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
        if let Some((idx, name)) = first_violation {
            let text = format!("Invariant {} is violated by the initial state:\n{}", name, self.state_text(&self.states[idx].vals));
            self.rep.error(ec::TLC_INVARIANT_VIOLATED_INITIAL, &text);
            self.stats(self.states.len());
            return Err(Stop::Exit(ec::exit_status::VIOLATION_SAFETY));
        }
        // ---- breadth-first search
        let next = setup.next.first();
        let mut head = 0usize;
        while head < self.states.len() {
            let cur = self.states[head].vals.clone();
            let cur_level = self.states[head].level;
            let mut succs: Vec<(Vec<Value>, Option<Rc<str>>)> = vec![];
            let mut incomplete: Option<Vec<Value>> = None;
            if let Some(nx) = next {
                let buf = RefCell::new(vec![Value::Undef; nvars]);
                let default_label: Rc<str> = Rc::from(format!(
                    "<{} line {}, col {} to line {}, col {} of module {}>",
                    nx.name, nx.loc.bl, nx.loc.bc, nx.loc.el, nx.loc.ec, nx.module
                ));
                *ev.cur_label.borrow_mut() = Some(default_label);
                ev.splitting.set(true);
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
            self.outdeg.push(nsucc as u32);
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
                let ok = match self.in_model(&st).and_then(|m| if m { self.action_ok(&cur, &st) } else { Ok(false) }) {
                    Ok(b) => b,
                    Err(e) => {
                        let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                        self.print_trace(head as u32);
                        return Err(Stop::Exit(code));
                    }
                };
                if !ok {
                    continue;
                }
                any_in_model = true;
                let fp = match self.fp(&st) {
                    Ok(f) => f,
                    Err(e) => {
                        let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                        return Err(Stop::Exit(code));
                    }
                };
                if self.fps.insert(fp) {
                    let level = cur_level + 1;
                    self.states.push(Rec { vals: st, parent: head as u32, label, level });
                    if level > self.max_level {
                        self.max_level = level;
                    }
                    let idx = self.states.len() - 1;
                    let vals = self.states[idx].vals.clone();
                    match self.check_invariants(&vals) {
                        Ok(None) => {}
                        Ok(Some(name)) => {
                            self.flush_output();
                            self.rep.error(ec::TLC_INVARIANT_VIOLATED_BEHAVIOR, &format!("Invariant {} is violated.", name));
                            self.print_trace(idx as u32);
                            let left = self.states.len() - head - 1;
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
            let _ = any_in_model;
            head += 1;
        }
        self.flush_output();
        Ok(())
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
    };
    let r = ck.run();
    match r {
        Ok(()) => {
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
