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
    /// per state: how many entries of `live_succ` are generated successors (the stuttering step is appended after them)
    live_gen_len: Vec<usize>,
    /// with a VIEW: the successor state actually produced by each recorded transition (parallel to `live_succ`)
    live_edge: Vec<Vec<Rc<Vec<Value>>>>,
    live_inits: Vec<u32>,
    /// fingerprint -> state index (only with liveness)
    fp_index: HashMap<u64, u32>,
    /// a Java exception the alias `_format` of the state being printed would throw (`String.format`), printed after the error
    fmt_exc: Option<(String, String)>,
    /// per processed state (in BFS order): (states generated, distinct states, depth) once its successors were added
    /// Java: `printSummary(false, ..)` after a failure while the initial states were processed: how many were handled
    init_fail: Option<u64>,
    /// the exception escaped `modelCheckImpl`: `TLC.process` reports it and no summary follows
    no_summary: bool,
    /// the state being expanded (an error then ends the run with the summary of `printSummary(false, ..)`)
    cur_head: Option<usize>,
    /// does the specification draw random numbers (`RandomElement`, `Randomization`)?
    uses_random: bool,
    /// Java: after the failed evaluation of an invariant / action property the replay of the state is silent and `printSummary(true)` follows
    outdeg_on_exit: bool,
    stats_done: bool,
    proc_log: Vec<(u64, usize, u32)>,
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

    // ---- POSTCONDITION with the counterexample (Java: Worker.doPostCondition, LiveWorker.printTrace, ModelChecker.modelCheckImpl)

    /// Java: `Tool.evalAlias(.., prefix)` binds `TLCExt!Trace` to the behavior up to and including the state being printed: the states
    /// `chain[..=n]` (state `n` is `last` when `n == chain.len()`)
    fn bind_alias_trace(&self, chain: &[u32], n: usize, last: Option<&[Value]>) {
        if self.setup.alias.is_none() {
            return;
        }
        let mut recs: Vec<Value> = chain.iter().take(n + 1).map(|&i| self.state_record(&self.states[i as usize].vals)).collect();
        if let Some(l) = last {
            recs.push(self.state_record(l));
        }
        *self.setup.ev.alias_trace.borrow_mut() = Some(recs);
    }

    /// Java: `TLCStateInfo.toRecordValue`: a state as the record `[var |-> value]`
    fn state_record(&self, vals: &[Value]) -> Value {
        Value::record(self.setup.vars.iter().zip(vals.iter()).map(|(v, x)| (tla_sany::intern::intern(&v.name), x.clone())).collect())
    }

    /// Java: `RecordValue(Action)`: `[name |-> .., location |-> [beginLine, beginColumn, endLine, endColumn, module]]` and, for an
    /// action with parameters, `context` and `parameters`; the unknown action has the location of the built-ins
    fn action_record(&self, l: &Option<LabelSpec>) -> Value {
        use tla_sany::intern::intern;
        let ev = &self.setup.ev;
        let loc_rec = |bl: u32, bc: u32, el: u32, ec: u32, module: &str| {
            Value::record(vec![
                (intern("beginLine"), Value::Int(bl as i32)),
                (intern("beginColumn"), Value::Int(bc as i32)),
                (intern("endLine"), Value::Int(el as i32)),
                (intern("endColumn"), Value::Int(ec as i32)),
                (intern("module"), Value::str(module)),
            ])
        };
        match l {
            None => Value::record(vec![(intern("name"), Value::str("UnnamedAction")), (intern("location"), loc_rec(0, 0, 0, 0, "--TLA+ BUILTINS--"))]),
            Some(l) => {
                let location = match ev.node_info.borrow().get(&l.stop) {
                    Some(i) => loc_rec(i.loc.bl as u32, i.loc.bc as u32, i.loc.el as u32, i.loc.ec as u32, &i.module),
                    None => loc_rec(0, 0, 0, 0, "--TLA+ BUILTINS--"),
                };
                let mut f = vec![(intern("name"), Value::str(&l.base.name)), (intern("location"), location)];
                if !l.base.params.is_empty() {
                    let ctx: Vec<(u32, Value)> = l.base.pnames.iter().zip(l.base.params.iter()).map(|(n, v)| (intern(n), v.clone())).collect();
                    f.push((intern("context"), Value::record(ctx)));
                    f.push((intern("parameters"), Value::tuple(l.base.pnames.iter().map(|n| Value::str(n)).collect())));
                }
                Value::record(f)
            }
        }
    }

    /// Java: `CounterExample(trace, action, loopOrdinal)`: the graph `[state |-> {<<n, state>>}, action |-> {<<s, action, t>>}]`;
    /// `back` closes a lasso: the 0-based index of the state the loop returns to and the action that takes it there
    fn counter_example_value(&self, recs: &[Value], labels: &[Option<LabelSpec>], back: Option<(usize, Option<LabelSpec>)>) -> Value {
        use tla_sany::intern::intern;
        let nums: Vec<Value> = recs.iter().enumerate().map(|(i, r)| Value::tuple(vec![Value::Int(i as i32 + 1), r.clone()])).collect();
        let mut edges = vec![];
        for i in 1..recs.len() {
            edges.push(Value::tuple(vec![nums[i - 1].clone(), self.action_record(&labels[i]), nums[i].clone()]));
        }
        if let (Some((pos, l)), Some(last)) = (back, nums.last()) {
            edges.push(Value::tuple(vec![last.clone(), self.action_record(&l), nums[pos].clone()]));
        }
        let set = |v: Vec<Value>| Value::set_from(v).unwrap_or(Value::Bool(false));
        Value::record(vec![(intern("action"), set(edges)), (intern("state"), set(nums))])
    }

    /// Java: `Tool.evalAlias`: the record the ALIAS makes of a trace state (the state itself when there is no ALIAS), `None` for a
    /// failed evaluation is reported as the extra field `_ALIASEvalError`
    fn alias_record(&mut self, level: usize, vals: &[Value], succ: &[Value]) -> Value {
        let setup = self.setup;
        let alias = match &setup.alias {
            Some(a) => a,
            None => return self.state_record(vals),
        };
        let ev = setup.ev.clone();
        let saved = ev.counters.get();
        let mut c = saved;
        c[0] = level as i64;
        ev.counters.set(c);
        let r = setup.run_top(alias, vals, succ).and_then(|v| v.force_fcn()).and_then(|v| v.normalize());
        ev.counters.set(saved);
        self.flush_output();
        match r {
            Ok(v) => v,
            Err(e) => {
                let mut f: Vec<(u32, Value)> = setup.vars.iter().zip(vals.iter()).map(|(v, x)| (tla_sany::intern::intern(&v.name), x.clone())).collect();
                f.push((tla_sany::intern::intern("_ALIASEvalError"), Value::str(&e.msg)));
                Value::record(f)
            }
        }
    }

    /// the states on the path to the state `parent`, followed by `last`
    fn path_states(&self, parent: Option<u32>, last: Option<&[Value]>) -> Vec<Vec<Value>> {
        let mut chain = vec![];
        let mut i = parent.unwrap_or(NONE);
        while i != NONE {
            chain.push(i);
            i = self.states[i as usize].parent;
        }
        chain.reverse();
        let mut out: Vec<Vec<Value>> = chain.iter().map(|&i| self.states[i as usize].vals.clone()).collect();
        if let Some(l) = last {
            out.push(l.to_vec());
        }
        out
    }

    /// the action that produced each state of a behavior (`None` for the first one and for a step that cannot be recomputed)
    fn trace_labels(&mut self, states: &[Vec<Value>]) -> Vec<Option<LabelSpec>> {
        let mut labels: Vec<Option<LabelSpec>> = vec![None];
        for i in 1..states.len() {
            let l = match self.fp(&states[i]) {
                Ok(fp) => self.step(&states[i - 1], i as i64, fp).and_then(|(_, l)| l),
                Err(_) => None,
            };
            labels.push(l);
        }
        labels
    }

    /// Java: `checkPostConditionWithCounterExample`: the POSTCONDITION is evaluated with `TLCExt!CounterExample` bound to `ce`; its
    /// failure is reported but does not change the result of the run
    fn run_post_with(&mut self, ce: Value) {
        let setup = self.setup;
        let ev = setup.ev.clone();
        *ev.counter_example.borrow_mut() = Some(ce);
        let _ = self.check_postconditions(setup);
        *ev.counter_example.borrow_mut() = None;
    }

    /// Java: `Worker.doPostCondition` after a safety violation: the behavior up to `parent` followed by `last`
    fn post_after_trace(&mut self, parent: Option<u32>, last: Option<&[Value]>) {
        if self.setup.postconditions.is_empty() {
            return;
        }
        let states = self.path_states(parent, last);
        if states.is_empty() {
            return;
        }
        let labels = self.trace_labels(&states);
        let mut recs = vec![];
        for i in 0..states.len() {
            let succ = states.get(i + 1).unwrap_or(&states[i]).clone();
            recs.push(self.alias_record(i + 1, &states[i], &succ));
        }
        let ce = self.counter_example_value(&recs, &labels, None);
        self.run_post_with(ce);
    }

    /// Java: `LiveWorker.printTrace`: the lasso (`back`: where the loop returns to and by which action) as a counterexample
    fn post_after_lasso(&mut self, actual: &[(Vec<Value>, Option<LabelSpec>)], back: Option<(usize, Option<LabelSpec>)>) {
        if self.setup.postconditions.is_empty() {
            return;
        }
        let recs: Vec<Value> = actual.iter().map(|(v, _)| self.state_record(v)).collect();
        let labels: Vec<Option<LabelSpec>> = actual.iter().map(|(_, l)| l.clone()).collect();
        let ce = self.counter_example_value(&recs, &labels, back);
        self.run_post_with(ce);
    }

    /// Java: `Tool.checkPostConditionWithContext`: POSTCONDITION(S) and `_POSSIBLE` checks, evaluated once the state
    /// space has been explored. Returns the exit code of the first postcondition that is false or fails.
    fn check_postconditions(&mut self, setup: &Setup) -> Option<i32> {
        for (top, loc, possible) in &setup.postconditions {
            let r = setup.run_top(top, &setup.ev.empty(), &setup.ev.empty());
            self.flush_output();
            let (code, text) = match r {
                Ok(Value::Bool(true)) => continue,
                Ok(Value::Bool(false)) => {
                    if *possible {
                        (
                            ec::TLC_POSSIBLE_UNWITNESSED,
                            format!(
                                "The _POSSIBLE predicate {} at {} was never witnessed.
Others may be unwitnessed too; only witnessed predicates appear with a
non-zero count in the record printed above.
See https://explain.tlapl.us/possible-conditions for additional details.",
                                top.name, loc
                            ),
                        )
                    } else {
                        (ec::TLC_POSTCONDITION_FALSE, format!("Postcondition {} at {} is false.", top.name, loc))
                    }
                }
                Ok(other) => (
                    ec::TLC_POSTCONDITION_EVALUATION_ERROR,
                    format!("Evaluating postcondition {} at {} failed.
The postcondition evaluated to the non-boolean value
{}", top.name, loc, other.to_tla()),
                ),
                Err(e) => (ec::TLC_POSTCONDITION_EVALUATION_ERROR, format!("Evaluating postcondition {} at {} failed.
{}", top.name, loc, e.msg)),
            };
            self.flush_output();
            self.rep.error(code, &text);
            return Some(ec::error_constant_to_exit_status(code));
        }
        None
    }

    fn flush_output(&mut self) {
        let lines: Vec<String> = self.setup.ev.out.borrow_mut().drain(..).collect();
        for l in lines {
            self.rep.raw(&l);
        }
        let warns: Vec<(i32, String)> = self.setup.ev.warnings.borrow_mut().drain(..).collect();
        for (code, text) in warns {
            self.rep.warning(code, &text);
        }
    }

    /// Java: TLCStateMut.toString: `/\ var = ppr(value)` lines (a lone variable prints without the `/\`)
    fn state_text(&self, vals: &[Value]) -> String {
        // Java: TLCStateMut.toString with `-view`: the value of the VIEW is printed (`OpApplNode.toString(IValue)`: a tuple with one
        // component per variable the VIEW depends on prints them as `/\ var = value` in declaration order)
        if self.opts.use_view {
            if let Some(view) = &self.setup.view {
                if let Ok(v) = self.setup.run_top(view, vals, &self.setup.ev.empty()) {
                    let (vs, nconst) = &self.setup.view_params;
                    if let Value::Tuple(t) = &v {
                        if t.len() == vs.len() + nconst {
                            let mut s = String::new();
                            for (i, var) in vs.iter().enumerate() {
                                s.push_str(&format!("/\\ {} = {}\n", self.setup.vars[*var as usize].name, tlc_core::pprint::ppr(&t[i].to_tla())));
                            }
                            return s;
                        }
                    }
                    return format!("{}\n", tlc_core::pprint::ppr(&v.to_tla()));
                }
            }
        }
        let mut s = String::new();
        let single = self.setup.vars.len() == 1;
        for (i, v) in self.setup.vars.iter().enumerate() {
            // Java: `Values.ppr(null)` for a variable that is not assigned (an incomplete successor state)
            let val = if matches!(vals[i], Value::Undef) { "null".to_string() } else { tlc_core::pprint::ppr(&vals[i].to_tla()) };
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
        // Java: the values an ALIAS builds are lazy: they are evaluated (while the state is printed) at the level of that state
        let ev = self.setup.ev.clone();
        let saved = ev.counters.get();
        let mut c = saved;
        c[0] = level as i64;
        ev.counters.set(c);
        let r = self.state_text_at_inner(vals, succ);
        ev.counters.set(saved);
        r
    }

    fn state_text_at_inner(&mut self, vals: &[Value], succ: &[Value]) -> String {
        let setup = self.setup;
        let alias = match &setup.alias {
            Some(a) => a,
            None => return self.state_text(vals),
        };
        let r = setup.run_top(alias, vals, succ);
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
                        // both arguments of `String.format(format, key, value)` are strings
                        Some(c) if matches!(c, 'd' | 'o' | 'x' | 'X' | 'f' | 'e' | 'E' | 'g' | 'G' | 'c') => {
                            if self.fmt_exc.is_none() {
                                self.fmt_exc = Some(("java.util.IllegalFormatConversionException".to_string(), format!("{} != java.lang.String", c)));
                            }
                            it.next();
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

    /// Java: `ModelChecker.modelCheckImpl`, `catch (Throwable e)` around `doInit`: an exception raised while an initial state is
    /// processed (constraints, fingerprint, invariants, implied initial predicates) is reported together with that state
    /// (`TLC_INITIAL_STATE`); the replay with the call-stack tool then names the nested expressions (`TLC_NESTED_EXPRESSION`).
    fn report_init_state_error(&mut self, e: &TlcErr, st: &[Value]) -> i32 {
        self.flush_output();
        if e.not_ported {
            self.rep.error(mp::NOT_PORTED, &e.msg);
            return 199;
        }
        if is_eval_exception(e.code) {
            // Java: an `EvalException` (thrown by the TLC modules) is not a `TLCRuntimeException`: `doInit` does not record the
            // initial state, so the failure is reported without it
            self.rep.error(ec::GENERAL, &e.java_message());
        } else {
            let text = format!("{}\nWhile working on the initial state:\n{}", e.java_message(), self.state_text(st));
            self.rep.error(ec::TLC_INITIAL_STATE, &text);
        }
        // Java: the replay with the call-stack tool prints the nested expressions the failure passed
        let stack = match self.replay_init_error(st) {
            Some(e2) => self.setup.ev.call_stack_text(&e2),
            None => self.setup.ev.call_stack_text(e),
        };
        self.rep.error(
            ec::TLC_NESTED_EXPRESSION,
            &format!("The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n{}", stack),
        );
        ec::error_constant_to_exit_status(ec::TLC_NESTED_EXPRESSION)
    }

    /// Java: `ModelChecker.modelCheckImpl`, `catch (Throwable e)` around `doInit`, for an exception of `LiveCheck.addInitState`: the
    /// state is reported, but the replay with the call-stack tool finds the initial state in the fingerprint set already, does not
    /// evaluate the liveness predicates again and completes: the exit status stays the one of the original error
    fn report_init_state_live_error(&mut self, e: &TlcErr, st: &[Value]) -> i32 {
        self.flush_output();
        if e.not_ported {
            self.rep.error(mp::NOT_PORTED, &e.msg);
            return 199;
        }
        let text = format!("{}\nWhile working on the initial state:\n{}", e.msg, self.state_text(st));
        self.rep.error(ec::TLC_INITIAL_STATE, &text);
        if is_eval_exception(e.code) {
            ec::error_constant_to_exit_status(ec::GENERAL)
        } else {
            ec::error_constant_to_exit_status(e.code)
        }
    }

    /// Java: `ModelChecker.doNextFailed` (after an invariant failed to evaluate on a successor): the state is expanded again with the
    /// call-stack tool, in the same order.  The successors that were stored by the first pass are known; every other one is stored and
    /// has its invariants evaluated, and the first failure there is the `FingerprintException` of the replay.  Returns the exit status.
    fn replay_failed_invariant(&mut self, rest: &mut dyn Iterator<Item = (Vec<Value>, Option<LabelSpec>)>, head: usize, cur_level: u32) -> i32 {
        let cur = self.states[head].vals.clone();
        // the state whose invariants failed and every state stored by the replay are not queued
        let mut not_queued = 1usize;
        let mut status = ec::exit_status::FAILURE_SAFETY_EVAL;
        for (st, label) in rest {
            let in_model = self.in_model(&st).and_then(|m| if m { self.action_ok(&cur, &st) } else { Ok(false) });
            if !matches!(in_model, Ok(true)) {
                continue;
            }
            let Ok(fp) = self.fp(&st) else { continue };
            if !self.fps.insert(fp) {
                continue;
            }
            self.states.push(Rec { vals: st, parent: head as u32, label, level: cur_level + 1 });
            not_queued += 1;
            let vals = self.states.last().unwrap().vals.clone();
            match self.check_invariants(&vals) {
                Ok(None) => not_queued -= 1,
                Ok(Some(_)) => break,
                Err((e2, _)) => {
                    self.flush_output();
                    self.rep.error(
                        ec::TLC_FINGERPRINT_EXCEPTION,
                        &format!("TLC was unable to fingerprint.

Fingerprint Stack Trace:


Reason:
{}", e2.msg),
                    );
                    status = ec::error_constant_to_exit_status(ec::TLC_FINGERPRINT_EXCEPTION);
                    break;
                }
            }
        }
        let left = (self.states.len() - head - 1).saturating_sub(not_queued);
        self.stats(left);
        status
    }

    /// Java: printing the state of the error report (`TLCState.toString`) normalizes its set enumerations: when their elements cannot be
    /// compared, that fails inside the exception handler of `modelCheckImpl`, so the exception escapes to `TLC.process` which reports
    /// it as an unexpected exception (the `TLCRuntimeException` shown as a `RuntimeException`)
    fn state_not_printable(&mut self, st: &[Value]) -> Option<i32> {
        let err = st.iter().find_map(|v| v.check_printable().err())?;
        self.no_summary = true;
        self.flush_output();
        self.rep.error(
            ec::GENERAL,
            &format!("TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: {}", err.msg),
        );
        Some(ec::error_constant_to_exit_status(ec::GENERAL))
    }

    /// the failure happened while the initial state was fingerprinted: the replay reports a `FingerprintException`
    fn report_init_state_error_fp(&mut self, e: &TlcErr, st: &[Value]) -> i32 {
        self.flush_output();
        if e.not_ported {
            self.rep.error(mp::NOT_PORTED, &e.msg);
            return 199;
        }
        if let Some(code) = self.state_not_printable(st) {
            return code;
        }
        let text = format!("{}
While working on the initial state:
{}", e.msg, self.state_text(st));
        self.rep.error(ec::TLC_INITIAL_STATE, &text);
        self.rep.error(
            ec::TLC_FINGERPRINT_EXCEPTION,
            &format!("TLC was unable to fingerprint.

Fingerprint Stack Trace:

Reason:
{}", e.msg),
        );
        ec::error_constant_to_exit_status(ec::TLC_FINGERPRINT_EXCEPTION)
    }

    fn report_err(&mut self, e: &TlcErr, default_exit: i32) -> i32 {
        self.flush_output();
        if e.not_ported {
            self.rep.error(mp::NOT_PORTED, &e.msg);
            return 199;
        }
        let msg: &str = if e.code == ec::SYSTEM_STACK_OVERFLOW { STACK_OVERFLOW_TEXT } else { &e.msg };
        self.rep.error(e.code, msg);
        match e.code {
            ec::TLC_VALUE_ASSERT_FAILED => ec::exit_status::VIOLATION_ASSERT,
            ec::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM => ec::exit_status::ERROR_CONFIG_PARSE,
            ec::SYSTEM_STACK_OVERFLOW => ec::exit_status::ERROR,
            _ => default_exit,
        }
    }

    fn in_model(&self, vals: &[Value]) -> R<bool> {
        for (i, c) in self.setup.constraints.iter().enumerate() {
            match self.setup.run_top(c, vals, &self.setup.ev.empty())? {
                Value::Bool(true) => {}
                Value::Bool(false) => return Ok(false),
                // Java: `Tool.isInModel`: `Assert.fail(EC.TLC_EXPECTED_VALUE, {"boolean", constraint.toString()}, constraint)`
                _ => return fail_code(ec::TLC_EXPECTED_VALUE, format!("TLC expected a boolean value, but did not find one. {}", self.setup.constraint_exprs[i])),
            }
        }
        Ok(true)
    }

    fn action_ok(&self, cur: &[Value], succ: &[Value]) -> R<bool> {
        for (i, c) in self.setup.action_constraints.iter().enumerate() {
            match self.setup.run_top(c, cur, succ)? {
                Value::Bool(true) => {}
                Value::Bool(false) => return Ok(false),
                _ => return fail_code(ec::TLC_EXPECTED_VALUE, format!("TLC expected a boolean value, but did not find one. {}", self.setup.action_constraint_exprs[i])),
            }
        }
        Ok(true)
    }

    fn print_trace(&mut self, idx: u32) {
        self.replay_init();
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
                self.transition_label(&pred, n as i64, &cur)
            };
            let nx = chain.get(n + 1).copied().unwrap_or(si);
            let (cur, succ) = (self.states[si as usize].vals.clone(), self.states[nx as usize].vals.clone());
            self.bind_alias_trace(&chain, n, None);
            let body = self.state_text_at(n + 1, &cur, &succ);
            *self.setup.ev.alias_trace.borrow_mut() = None;
            if self.report_fmt_exc() {
                return;
            }
            let text = format!("{}: {}\n{}", n + 1, label, body);
            self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
        }
    }

    /// print the exception a `_format` alias threw while a state was printed (Java: `MP.printError(EC.GENERAL, e)`)
    fn report_fmt_exc(&mut self) -> bool {
        match self.fmt_exc.take() {
            Some((cls, msg)) => {
                self.rep.error(
                    ec::GENERAL,
                    &format!(
                        "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a {} : {}",
                        cls, msg
                    ),
                );
                true
            }
            None => false,
        }
    }

    /// check the invariants on a state; `Some(name)` if one is violated
    fn check_invariants(&self, vals: &[Value]) -> Result<Option<String>, (Box<TlcErr>, String)> {
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
                            fp_exc: false,
                            frames: vec![],
                            pass: false,
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
    fn check_implied_inits(&self, vals: &[Value]) -> Result<Option<String>, (Box<TlcErr>, String)> {
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
    fn check_implied_actions(&self, cur: &[Value], succ: &[Value]) -> Result<Option<String>, (Box<TlcErr>, String)> {
        for p in &self.setup.implied_actions {
            match self.setup.run_top(p, cur, succ) {
                Ok(Value::Bool(true)) => {}
                Ok(_) => return Ok(Some(p.name.clone())),
                Err(e) => return Err((e, p.name.clone())),
            }
        }
        Ok(None)
    }

    /// Java: `ModelChecker.modelCheckImpl`: the initial predicate failed to evaluate: the message of the exception is printed as a
    /// general error and the replay with the call-stack tool names the nested expressions
    fn report_init_failure(&mut self, e: &TlcErr) -> i32 {
        if e.not_ported || e.code == ec::SYSTEM_STACK_OVERFLOW || e.code == ec::TLC_VALUE_ASSERT_FAILED || e.code == ec::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM || e.code == ec::GENERAL {
            let code = self.report_err(e, ec::exit_status::FAILURE_SPEC_EVAL);
            if !e.not_ported && e.code != ec::SYSTEM_STACK_OVERFLOW {
                self.print_nested_expressions(e);
            }
            return code;
        }
        self.flush_output();
        self.rep.error(ec::GENERAL, &e.java_message());
        self.print_nested_expressions(e);
        ec::exit_status::FAILURE_SPEC_EVAL
    }

    /// Java: `ModelChecker.doNextFailed`: the exception that ended the expansion of a state is reported under its own code when it is an
    /// `EvalException` (thrown by the TLC modules), otherwise as an unexpected exception (a `TLCRuntimeException` is shown as a
    /// `RuntimeException`); returns the exit status
    fn report_next_failure(&mut self, e: &TlcErr) -> i32 {
        if e.not_ported || e.code == ec::SYSTEM_STACK_OVERFLOW || e.code == ec::TLC_VALUE_ASSERT_FAILED || e.code == ec::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM {
            return self.report_err(e, ec::exit_status::FAILURE_SPEC_EVAL);
        }
        self.flush_output();
        if is_eval_exception(e.code) {
            self.rep.error(e.code, &e.msg);
        } else {
            let text = format!("TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: {}", e.java_message());
            self.rep.error(ec::GENERAL, &text);
        }
        ec::exit_status::FAILURE_SPEC_EVAL
    }

    /// Java: the replay with the call-stack tool names the nested expressions the failure passed (`TLC_NESTED_EXPRESSION`)
    fn print_nested_expressions(&mut self, e: &TlcErr) {
        let stack = self.setup.ev.call_stack_text(e);
        self.rep.error(
            ec::TLC_NESTED_EXPRESSION,
            &format!("The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n{}", stack),
        );
    }

    /// the checks the model checker applies to an initial state, in its order: the failure of the first one that raises an error
    fn init_state_failure(&self, st: &[Value]) -> Option<Box<TlcErr>> {
        match self.in_model(st) {
            Err(e) => return Some(e),
            Ok(false) => return None,
            Ok(true) => {}
        }
        if let Err(e) = self.fp(st) {
            return Some(e);
        }
        if let Err((e, _)) = self.check_invariants(st) {
            return Some(e);
        }
        if let Err((e, _)) = self.check_implied_inits(st) {
            return Some(e);
        }
        None
    }

    /// Java: `ModelChecker.doInit(cTool, true)`: the initial predicate is evaluated again with the call-stack tool; the state is checked
    /// again inside the continuation of the enumeration, so the failure carries the frames of the nodes being decomposed
    fn replay_init_error(&self, st: &[Value]) -> Option<Box<TlcErr>> {
        let setup = self.setup;
        let ev = setup.ev.clone();
        let nvars = setup.vars.len();
        for top in &setup.init {
            let buf = RefCell::new(vec![Value::Undef; nvars]);
            let r = ev.with_frame(top.nslots.get(), |ev| {
                ev.epoch.set(ev.epoch.get() + 1);
                ev.enum_action(&top.ex, Mode::Init, &ev.empty(), &buf, &mut || {
                    let cur = buf.borrow().clone();
                    if cur.len() == st.len() && cur.iter().zip(st.iter()).all(|(a, b)| a.eq_val(b).unwrap_or(false)) {
                        if let Some(e2) = self.init_state_failure(&cur) {
                            return Err(e2);
                        }
                    }
                    Ok(())
                })
            });
            if let Err(e2) = r {
                return Some(e2);
            }
        }
        None
    }

    /// Java: `Tool.getState(fp)`: the states of a trace are recreated from their fingerprints, starting with the initial states,
    /// which evaluates the initial predicate again (with its side effects: `TLCSet` registers, `Print` output)
    fn replay_init(&mut self) {
        let setup = self.setup;
        let ev = setup.ev.clone();
        let nvars = setup.vars.len();
        for top in &setup.init {
            let buf = RefCell::new(vec![Value::Undef; nvars]);
            let _ = ev.with_frame(top.nslots.get(), |ev| {
                ev.epoch.set(ev.epoch.get() + 1);
                ev.enum_action(&top.ex, Mode::Init, &ev.empty(), &buf, &mut || Ok(()))
            });
        }
        self.flush_output();
    }

    /// the behavior leading to `parent`, followed by the state `vals` reached by `label`
    fn print_trace_ext(&mut self, parent: u32, vals: &[Value]) {
        self.print_trace_ext_l(parent, vals, None)
    }

    /// like `print_trace_ext`; `last_label` names the action that produced `vals` when it cannot be recomputed from its fingerprint
    fn print_trace_ext_l(&mut self, parent: u32, vals: &[Value], last_label: Option<String>) {
        self.replay_init();
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
                self.transition_label(&pred, n as i64, &cur)
            };
            let cur = self.states[si as usize].vals.clone();
            let succ = match chain.get(n + 1) {
                Some(&nx) => self.states[nx as usize].vals.clone(),
                None => vals.to_vec(),
            };
            self.bind_alias_trace(&chain, n, None);
            let body = self.state_text_at(n + 1, &cur, &succ);
            *self.setup.ev.alias_trace.borrow_mut() = None;
            if self.report_fmt_exc() {
                return;
            }
            let text = format!("{}: {}\n{}", n + 1, l, body);
            self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
        }
        let l = match (last_label, chain.last()) {
            (Some(l), _) => l,
            (None, Some(&last)) => {
                let pred = self.states[last as usize].vals.clone();
                self.transition_label(&pred, chain.len() as i64, vals)
            }
            (None, None) => "<Next>".to_string(),
        };
        self.bind_alias_trace(&chain, chain.len(), Some(vals));
        let body = self.state_text_at(chain.len() + 1, vals, vals);
        *self.setup.ev.alias_trace.borrow_mut() = None;
        if self.report_fmt_exc() {
            return;
        }
        let text = format!("{}: {}\n{}", chain.len() + 1, l, body);
        self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
    }

    fn stats(&mut self, left: usize) {
        self.stats_done = true;
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
        ev.fp_index.set(self.opts.fp_index.max(0) as usize);
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
        // Java: TLCGetSet.TLCGet("spec"): the initial predicates, actions, invariants, ... as found by spec processing
        {
            use tla_sany::intern::intern;
            let loc_rec = |l: &tla_sany::ast::Loc, module: &str| {
                Value::record(vec![
                    (intern("beginLine"), Value::Int(l.bl as i32)),
                    (intern("beginColumn"), Value::Int(l.bc as i32)),
                    (intern("endLine"), Value::Int(l.el as i32)),
                    (intern("endColumn"), Value::Int(l.ec as i32)),
                    (intern("module"), Value::str(module)),
                ])
            };
            let named = |name: &str, l: &tla_sany::ast::Loc, module: &str| {
                Value::record(vec![(intern("name"), Value::str(name)), (intern("location"), loc_rec(l, module))])
            };
            let set_of = |tops: &[tlc_core::spec::Top]| Value::set_from(tops.iter().map(|t| named(&t.name, &t.loc, &t.module)).collect()).unwrap_or(Value::Bool(false));
            let vars: Vec<Value> = setup.vars.iter().map(|v| named(&v.name, &v.loc, &v.module)).collect();
            let rec = Value::record(vec![
                (intern("inits"), set_of(&setup.init)),
                (intern("actions"), set_of(&setup.next)),
                (intern("temporals"), Value::set_from(vec![]).unwrap_or(Value::Bool(false))),
                (intern("invariants"), set_of(&setup.invariants)),
                (intern("impliedinits"), set_of(&setup.implied_inits)),
                (intern("impliedactions"), set_of(&setup.implied_actions)),
                (
                    intern("impliedtemporals"),
                    Value::set_from(setup.implied_temporals.iter().map(|(n, l, m)| named(n, l, m)).collect()).unwrap_or(Value::Bool(false)),
                ),
                (intern("variables"), Value::set_from(vars).unwrap_or(Value::Bool(false))),
                (intern("actionconstraints"), set_of(&setup.action_constraints)),
                (intern("constraints"), set_of(&setup.constraints)),
            ]);
            ev.stats.borrow_mut().insert("spec".to_string(), rec);
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
                if e.code == ec::SYSTEM_STACK_OVERFLOW {
                    // Java: modelCheckImpl: the exception is reported as GENERAL and the replay names the (empty) call stack
                    self.flush_output();
                    self.rep.error(ec::GENERAL, STACK_OVERFLOW_TEXT);
                    self.rep.error(
                        ec::TLC_NESTED_EXPRESSION,
                        "The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\nThe error call stack is empty.",
                    );
                    self.init_fail = Some(0);
                    return Err(Stop::Exit(ec::error_constant_to_exit_status(ec::TLC_NESTED_EXPRESSION)));
                }
                let code = self.report_init_failure(&e);
                self.init_fail = Some(0);
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
        // Java: the initial states have level 1 (TLCGet("level") is 0 only while the initial predicate is evaluated)
        self.set_counters(1, 0);
        for (k_init, st) in inits.into_iter().enumerate() {
            // constraints are applied to the initial states as well
            match self.in_model(&st) {
                Ok(true) => {}
                Ok(false) => continue,
                Err(e) => {
                    let code = self.report_init_state_error(&e, &st);
                    self.init_fail = Some(k_init as u64 + 1);
                    return Err(Stop::Exit(code));
                }
            }
            let fp = match self.fp(&st) {
                Ok(f) => f,
                Err(e) => {
                    let code = self.report_init_state_error_fp(&e, &st);
                    self.init_fail = Some(k_init as u64 + 1);
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
                    // Java: LiveCheck.addInitState -> TableauLiveChecker.addInitState: (state, tnode) is a root node if the initial
                    // tableau node is consistent with the state, which evaluates the state predicates of the tableau node
                    let vals = self.states[idx as usize].vals.clone();
                    for o in &setup.live.oss {
                        if let Some(tb) = &o.tableau {
                            for t in 0..tb.init_cnt {
                                if let Err(e) = tb.nodes[t].is_consistent(&ev, &vals) {
                                    let code = self.report_init_state_live_error(&e, &vals);
                                    // Java: `printSummary` of the failed initialization: the states processed so far are queued
                                    self.generated = k_init as u64 + 1;
                                    self.max_level = 1;
                                    self.stats(self.states.len());
                                    return Err(Stop::Exit(code));
                                }
                            }
                        }
                    }
                }
                if self.opts.continue_after_error && first_violation.is_none() {
                    // Java: DoInitFunctor.addElement with `-continue`: every violated invariant of every initial state is reported
                    // and the exploration goes on
                    let idx = self.states.len() - 1;
                    let vals = self.states[idx].vals.clone();
                    let invs: Vec<(String, Result<Value, Box<TlcErr>>)> = setup
                        .invariants
                        .iter()
                        .map(|inv| (inv.name.clone(), setup.run_top(inv, &vals, &setup.ev.empty())))
                        .collect();
                    for (name, r) in invs {
                        match r {
                            Ok(Value::Bool(true)) => {}
                            Ok(Value::Bool(false)) => {
                                self.flush_output();
                                let st = self.state_text_at(1, &vals, &vals);
                                self.rep.error(ec::TLC_INVARIANT_VIOLATED_INITIAL, &format!("Invariant {} is violated by the initial state:
{}", name, st));
                                // Java: `ModelChecker.modelCheckImpl`: the POSTCONDITION sees the initial state as the counterexample
                                self.post_after_trace(None, Some(&vals));
                            }
                            Ok(_) => {}
                            Err(e) => {
                                let code = self.report_init_state_error(&e, &vals);
                                self.init_fail = Some(k_init as u64 + 1);
                                return Err(Stop::Exit(code));
                            }
                        }
                    }
                } else if first_violation.is_none() {
                    let idx = self.states.len() - 1;
                    let vals = self.states[idx].vals.clone();
                    match self.check_invariants(&vals) {
                        Ok(None) => match self.check_implied_inits(&vals) {
                            Ok(None) => {}
                            Ok(Some(name)) => first_violation = Some((idx, name, true)),
                            Err((e, _name)) => {
                                let code = self.report_init_state_error(&e, &vals);
                                self.init_fail = Some(k_init as u64 + 1);
                                return Err(Stop::Exit(code));
                            }
                        },
                        Ok(Some(name)) => first_violation = Some((idx, name, false)),
                        Err((e, _name)) => {
                            let code = self.report_init_state_error(&e, &vals);
                            self.init_fail = Some(k_init as u64 + 1);
                            return Err(Stop::Exit(code));
                        }
                    }
                }
            }
        }
        self.generated = init_generated;
        self.max_level = if self.states.is_empty() { 0 } else { 1 };
        if let Some((idx, name, is_prop)) = first_violation {
            // Java: `tool.evalAlias(curState, curState)`
            let iv = self.states[idx].vals.clone();
            let st = self.state_text_at(1, &iv, &iv);
            if is_prop {
                self.rep.error(ec::TLC_PROPERTY_VIOLATED_INITIAL, &format!("Property {} is violated by the initial state:
{}", name, st));
            } else {
                self.rep.error(ec::TLC_INVARIANT_VIOLATED_INITIAL, &format!("Invariant {} is violated by the initial state:
{}", name, st));
            }
            self.post_after_trace(Some(idx as u32), None);
            // Java: `modelCheckImpl` returns after a failed `doInit` without `printSummary`
            return Err(Stop::Exit(ec::error_constant_to_exit_status(if is_prop { ec::TLC_PROPERTY_VIOLATED_INITIAL } else { ec::TLC_INVARIANT_VIOLATED_INITIAL })));
        }
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
        // Java: ModelChecker.modelCheckImpl: finished if there is no next state predicate
        if setup.next.is_empty() && !self.states.is_empty() {
            self.flush_output();
            self.rep.error(ec::TLC_STATES_AND_NO_NEXT_ACTION, "No next state actions defined to generate successor states from.");
            return Err(Stop::Exit(ec::error_constant_to_exit_status(ec::TLC_STATES_AND_NO_NEXT_ACTION)));
        }
        // ---- breadth-first search
        let next = setup.next.first();
        let mut head = 0usize;
        while head < self.states.len() {
            self.cur_head = Some(head);
            if self.uses_random {
                // Java: `IdThread.setCurrentState`: the state whose successors are computed seeds the random choices
                *self.setup.ev.pred_state.borrow_mut() = Some(self.states[head].vals.clone());
                self.setup.ev.pred_id.set(self.setup.ev.pred_id.get() + 1);
            }
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
                *ev.cur_label.borrow_mut() = Some(LabelSpec { base: Rc::new(tlc_core::eval::LabelBase { name: std::sync::Arc::from(nx.name.as_str()), params: vec![], pnames: vec![] }), stop: Rc::as_ptr(&nx.ex) as usize });
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
                    let code = self.report_next_failure(&e);
                    if !e.not_ported {
                        self.print_trace(head as u32);
                        // Java: a StackOverflowError is not replayed (`keepCallStack` is false)
                        if e.code != ec::SYSTEM_STACK_OVERFLOW {
                            self.print_nested_expressions(&e);
                        }
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
                // Java: ModelChecker.doNextSetErr: the text names the action unless the next-state relation has a single one
                let (label, single) = self.incomplete_action(&cur);
                let plural = if names.len() > 1 { "s are" } else { " is" };
                let text = if single {
                    format!("Successor state is not completely specified by the next-state action. The following variable{} not defined: {}.\n", plural, names.join(", "))
                } else {
                    let aname = label.as_ref().map(|l| l.base.name.to_string()).unwrap_or_default();
                    format!("Successor state is not completely specified by action {} of the next-state relation. The following variable{} not defined: {}.\n", aname, plural, names.join(", "))
                };
                self.rep.error(ec::TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT, &text);
                let label_text = label.as_ref().map(|l| setup.ev.format_label(l));
                self.print_trace_ext_l(head as u32, &st, label_text);
                self.post_after_trace(Some(head as u32), Some(&st));
                // Java: the incomplete successor counts as generated; `printSummary(false, ..)` follows
                self.generated += 1;
                let left = self.states.len() - head - 1;
                self.stats(left);
                return Err(Stop::Exit(ec::exit_status::FAILURE_SPEC_EVAL));
            }
            let nsucc = succs.len();
            let mut unseen_count: u32 = 0;
            let mut any_in_model = false;
            if nsucc == 0 && self.opts.check_deadlock && setup.check_deadlock {
                self.rep.error(ec::TLC_DEADLOCK_REACHED, "Deadlock reached.");
                self.print_trace(head as u32);
                self.post_after_trace(Some(head as u32), None);
                self.generated += 0;
                self.stats(self.states.len() - head - 1);
                return Err(Stop::Exit(ec::exit_status::VIOLATION_DEADLOCK));
            }
            let mut succ_it = succs.into_iter();
            while let Some((st, label)) = succ_it.next() {
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
                            self.post_after_trace(Some(head as u32), Some(&st));
                            let left = self.states.len() - head - 1;
                            self.stats(left);
                            if !self.opts.continue_after_error {
                                return Err(Stop::Exit(ec::exit_status::VIOLATION_SAFETY));
                            }
                        }
                        Err((e, name)) if is_eval_exception(e.code) && !e.not_ported => {
                            // Java: `doNextEvalFailed` reports the cause inside the message of the failed invariant
                            self.flush_output();
                            self.rep.error(ec::TLC_INVARIANT_EVALUATION_FAILED, &format!("Evaluating invariant {} failed.\n{}", name, e.java_message()));
                            self.print_trace(head as u32);
                            self.outdeg.push(unseen_count);
                            self.outdeg_on_exit = true;
                            return Err(Stop::Exit(ec::exit_status::FAILURE_SAFETY_EVAL));
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
                            if e.not_ported {
                                let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                                return Err(Stop::Exit(code));
                            }
                            // Java: the worker fails to fingerprint the successor: the exception is reported, then the trace to the
                            // predecessor, then the replay's FingerprintException; `printSummary(false, ..)` follows
                            self.flush_output();
                            let text = format!(
                                "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException : {}",
                                e.msg
                            );
                            self.rep.error(ec::GENERAL, &text);
                            self.print_trace(head as u32);
                            self.rep.error(ec::GENERAL, &text);
                            self.rep.error(
                                ec::TLC_FINGERPRINT_EXCEPTION,
                                &format!("TLC was unable to fingerprint.\n\nFingerprint Stack Trace:\n\nReason:\n{}", e.msg),
                            );
                            let left = self.states.len() - head - 1;
                            self.stats(left);
                            return Err(Stop::Exit(ec::error_constant_to_exit_status(ec::TLC_FINGERPRINT_EXCEPTION)));
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
                                self.post_after_trace(Some(idx as u32), None);
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
                                if is_eval_exception(e.code) && !e.fp_exc && !e.not_ported {
                                    self.rep.error(ec::TLC_INVARIANT_EVALUATION_FAILED, &format!("Evaluating invariant {} failed.\n{}", name, e.java_message()));
                                    self.print_trace(idx as u32);
                                    // Java enqueues a successor only after its invariants were evaluated: the failing state is not queued
                                    let left = self.states.len() - head - 2;
                                    self.stats(left);
                                    self.outdeg.push(unseen_count);
                                    self.outdeg_on_exit = true;
                                    return Err(Stop::Exit(ec::exit_status::FAILURE_SAFETY_EVAL));
                                }
                                if e.fp_exc && !e.not_ported {
                                    // Java: `doNextEvalFailed` reports the cause inside the message; the failure is a `FingerprintException`:
                                    // the replay with the call-stack tool expands the state again
                                    self.rep.error(ec::TLC_INVARIANT_EVALUATION_FAILED, &format!("Evaluating invariant {} failed.
{}", name, e.msg));
                                    self.print_trace(idx as u32);
                                    let code = self.replay_failed_invariant(&mut succ_it, head, cur_level);
                                    return Err(Stop::Exit(code));
                                }
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
                            self.post_after_trace(Some(head as u32), Some(&sv));
                            let left = self.states.len() - head - 1 - usize::from(just_pushed);
                            self.stats(left);
                            return Err(Stop::Exit(ec::error_constant_to_exit_status(ec::TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR)));
                        }
                        Err((e, name)) if is_eval_exception(e.code) && !e.not_ported => {
                            self.flush_output();
                            self.rep.error(ec::TLC_ACTION_PROPERTY_EVALUATION_FAILED, &format!("Evaluating action property {} failed.\n{}", name, e.java_message()));
                            self.print_trace(head as u32);
                            self.outdeg.push(unseen_count + u32::from(just_pushed));
                            self.outdeg_on_exit = true;
                            return Err(Stop::Exit(ec::exit_status::FAILURE_SAFETY_EVAL));
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
                if self.live_gen_len.len() <= head {
                    self.live_gen_len.resize(head + 1, 0);
                }
                self.live_gen_len[head] = self.live_succ[head].len();
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
            if self.live {
                self.proc_log.push((self.generated, self.states.len(), self.max_level));
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
    fn transition_label(&mut self, pred: &[Value], level: i64, succ: &[Value]) -> String {
        let fp = match self.fp(succ) {
            Ok(f) => f,
            Err(_) => return "<Next>".to_string(),
        };
        match self.step(pred, level, fp) {
            Some((_, Some(l))) => self.setup.ev.format_label(&l),
            _ => "<Next>".to_string(),
        }
    }

    /// the action (label, split into the disjuncts of the next-state relation) that yields the first incomplete successor of
    /// `pred`, and whether the relation consists of a single action
    fn incomplete_action(&mut self, pred: &[Value]) -> (Option<LabelSpec>, bool) {
        let setup = self.setup;
        let ev = setup.ev.clone();
        let nx = match setup.next.first() {
            Some(n) => n,
            None => return (None, true),
        };
        let cur = pred.to_vec();
        let buf = RefCell::new(vec![Value::Undef; setup.vars.len()]);
        let mut found: Option<LabelSpec> = None;
        ev.epoch.set(ev.epoch.get() + 1);
        *ev.cur_label.borrow_mut() = Some(LabelSpec { base: Rc::new(tlc_core::eval::LabelBase { name: std::sync::Arc::from(nx.name.as_str()), params: vec![], pnames: vec![] }), stop: Rc::as_ptr(&nx.ex) as usize });
        ev.splitting.set(true);
        let _ = ev.with_frame(nx.nslots.get(), |ev| {
            ev.enum_action(&nx.ex, Mode::Next, &cur, &buf, &mut || {
                if found.is_none() && buf.borrow().iter().any(|v| matches!(v, Value::Undef)) {
                    found = ev.cur_label.borrow().clone();
                }
                Ok(())
            })
        });
        ev.splitting.set(false);
        self.flush_output();
        let single = match &found {
            Some(l) => l.stop == Rc::as_ptr(&nx.ex) as usize,
            None => true,
        };
        (found, single)
    }

    /// Java: `Tool.getState(fp, predecessor)`: the first successor of `pred` (in the order the actions yield them) whose
    /// fingerprint is `target_fp`, with the label of the action that yields it
    fn step(&mut self, pred: &[Value], level: i64, target_fp: u64) -> Option<(Vec<Value>, Option<LabelSpec>)> {
        let setup = self.setup;
        let ev = setup.ev.clone();
        if self.uses_random {
            *ev.pred_state.borrow_mut() = Some(pred.to_vec());
            ev.pred_id.set(ev.pred_id.get() + 1);
        }
        // Java: `TLCGet("level")` is the level of the state the actions are applied to (its position in the behavior)
        let saved = ev.counters.get();
        let mut c = saved;
        c[0] = level;
        ev.counters.set(c);
        let nx = setup.next.first()?;
        let cur = pred.to_vec();
        let nvars = setup.vars.len();
        let mut found: Option<(Vec<Value>, Option<LabelSpec>)> = None;
        let buf = RefCell::new(vec![Value::Undef; nvars]);
        ev.epoch.set(ev.epoch.get() + 1);
        *ev.cur_label.borrow_mut() = Some(LabelSpec { base: Rc::new(tlc_core::eval::LabelBase { name: std::sync::Arc::from(nx.name.as_str()), params: vec![], pnames: vec![] }), stop: Rc::as_ptr(&nx.ex) as usize });
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
        ev.counters.set(saved);
        self.flush_output();
        found
    }

    /// Java: `Worker.doNextCheckLiveness`: the successors of a state reach `LiveCheck.addNextState` in the slot order of a `SetOfStates`
    /// (open addressing by the state's fingerprint; a worker keeps the capacity it needed: `multiplier`).  Reproduced for states whose
    /// values this port can fingerprint like Java (`jfp`); returns false (the caller keeps another fixed order) otherwise.
    fn java_set_order(&mut self) -> Option<Vec<Vec<u32>>> {
        if !self.perms.is_empty() || self.setup.view.is_some() {
            return None;
        }
        let fp64 = tlc_core::jfp::fp64(self.opts.fp_index.max(0) as usize);
        let mut fps: Vec<u64> = Vec::with_capacity(self.states.len());
        for s in &self.states {
            match fp64.state_opt(&s.vals) {
                Some(f) => fps.push(f),
                None => return None,
            }
        }
        // the successors in generation order (without the stuttering step), for the nodes Java creates after their state was done
        let gen: Vec<Vec<u32>> = (0..self.live_succ.len())
            .map(|i| {
                let n = self.live_gen_len.get(i).copied().unwrap_or(0).min(self.live_succ[i].len());
                self.live_succ[i][..n].to_vec()
            })
            .collect();
        let mut multiplier = 1usize;
        for i in 0..self.live_succ.len() {
            if self.live_succ[i].is_empty() {
                continue;
            }
            let mut length = multiplier * 16;
            let mut slots: Vec<Option<u32>> = vec![None; length];
            let mut count = 0usize;
            let mut thresh = length / 2;
            // Java: SetOfStates.put0 / grow
            fn put0(slots: &mut Vec<Option<u32>>, count: &mut usize, fp: u64, node: u32) {
                let length = slots.len();
                let mut loc = ((fp as u32 as i32) & 0x7FFF_FFFF) as usize % length;
                loop {
                    match slots[loc] {
                        None => {
                            slots[loc] = Some(node);
                            *count += 1;
                            return;
                        }
                        Some(e) if e == node => return,
                        _ => {}
                    }
                    loc = (loc + 1) % length;
                }
            }
            let succ = self.live_succ[i].clone();
            for &t in &succ {
                if count >= thresh {
                    let old = std::mem::take(&mut slots);
                    length = (2 * length + 1).min(i32::MAX as usize);
                    thresh = length / 2;
                    slots = vec![None; length];
                    count = 0;
                    for n in old.into_iter().flatten() {
                        put0(&mut slots, &mut count, fps[n as usize], n);
                    }
                }
                put0(&mut slots, &mut count, fps[t as usize], t);
            }
            if length > multiplier * 16 {
                multiplier += 1;
            }
            self.live_succ[i] = slots.into_iter().flatten().collect();
        }
        Some(gen)
    }

    /// Java: `ModelChecker`: the final liveness check (`LiveCheck.finalCheck` -> `LiveWorker`)
    fn final_liveness_check(&mut self) -> SR<()> {
        let setup = self.setup;
        let ev = setup.ev.clone();
        let left = 0usize;
        let oss = &setup.live.oss;
        let t0 = std::time::Instant::now();
        // Java iterates the successors of a state in the order of a hash set (`SetOfStates`: slot = FP64 % capacity), an
        // order that cannot be reproduced here (our fingerprints and intern tokens differ); any fixed order is as good as
        // another.  The reverse generation order agrees with Java's counterexamples more often on the test corpus.
        let gen_lists = self.java_set_order();
        if gen_lists.is_none() {
            for (i, v) in self.live_succ.iter_mut().enumerate() {
                v.reverse();
                if i < self.live_edge.len() && self.live_edge[i].len() == v.len() {
                    self.live_edge[i].reverse();
                }
            }
        }
        let table = StateTable(&self.states, &self.live_edge);
        // Java: `LiveCheck.addNextState` finds the counterexample of a safety-like property while the state graph is explored
        let mut early: Option<(usize, crate::live::Shortcut)> = None;
        for (oi, o) in oss.iter().enumerate() {
            match crate::live::safety_shortcut(&ev, &table, &self.live_succ, gen_lists.as_deref(), &self.live_inits, o) {
                Ok(Some(hit)) => {
                    if early.as_ref().map_or(true, |(_, h)| hit.k < h.k) {
                        early = Some((oi, hit));
                    }
                }
                Ok(None) => {}
                Err(e) => {
                    self.flush_output();
                    let code = self.report_err(&e, ec::exit_status::FAILURE_SPEC_EVAL);
                    return Err(Stop::Exit(code));
                }
            }
        }
        if let Some((oi, hit)) = early {
            let lasso = crate::live::Lasso { cycle_pos: hit.states.len() - 1, states: hit.states.clone(), stuttering: false };
            self.print_lasso_ext(&lasso, &oss[oi], true);
            // Java: `printSummary(false, ..)` at the time the violation was found
            if let Some(&(generated, distinct, level)) = self.proc_log.get(hit.k) {
                self.generated = generated;
                self.states.truncate(distinct);
                self.max_level = level;
            }
            let left = self.states.len().saturating_sub(hit.k + 1);
            self.stats(left);
            return Err(Stop::Exit(ec::error_constant_to_exit_status(ec::TLC_INVARIANT_VIOLATED_BEHAVIOR)));
        }
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
        let graphs = match crate::live::build_all(&ev, &table, &self.live_succ, gen_lists.as_deref(), &self.live_inits, oss) {
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
        self.print_lasso_ext(lasso, oos, false)
    }

    /// `finite`: a counterexample of a safety-like property found while exploring (no loop marker follows the states)
    fn print_lasso_ext(&mut self, lasso: &crate::live::Lasso, oos: &tlc_core::liveness::oos::Oos, finite: bool) {
        self.replay_init();
        let setup = self.setup;
        let ev = setup.ev.clone();
        // the real behavior: every state is the successor of the previous printed state with the fingerprint of the node
        // (with a VIEW a node stands for several states)
        let fps: Vec<u64> = lasso.states.iter().map(|&i| self.fp(&self.states[i as usize].vals).unwrap_or(0)).collect();
        let mut actual: Vec<(Vec<Value>, Option<LabelSpec>)> = vec![(self.states[lasso.states[0] as usize].vals.clone(), None)];
        for i in 1..lasso.states.len() {
            let prev = actual[i - 1].0.clone();
            let next = match self.step(&prev, i as i64, fps[i]) {
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
            // Java: `Tool.evalAlias(.., prefix)` binds `TLCExt!Trace`: a state of the prefix sees the states before it, a state of the
            // cycle sees the states up to and including itself
            if setup.alias.is_some() {
                let upto = if n < lasso.cycle_pos { n } else { n + 1 };
                let recs: Vec<Value> = actual[..upto].iter().map(|(x, _)| self.state_record(x)).collect();
                *ev.alias_trace.borrow_mut() = Some(recs);
            }
            let body = self.state_text_at(n + 1, v, &succ);
            *ev.alias_trace.borrow_mut() = None;
            let text = format!("{}: {}\n{}", n + 1, label, body);
            self.rep.message(ec::TLC_STATE_PRINT2, mp::class::STATE, &text);
        }
        let cycle_num = lasso.cycle_pos + 1;
        if finite {
            self.post_after_lasso(&actual, None);
            return;
        }
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
            let last_label = actual.last().and_then(|(_, l)| l.clone());
            self.post_after_lasso(&actual, Some((lasso.cycle_pos, last_label)));
        } else {
            let last = actual.last().unwrap().0.clone();
            let back_label = self.step(&last, actual.len() as i64, fps[lasso.cycle_pos]).and_then(|(_, l)| l);
            let label = match &back_label {
                Some(l) => ev.format_label(l),
                None => "<Next>".to_string(),
            };
            self.rep.message(ec::TLC_BACK_TO_STATE, mp::class::STATE, &format!("{}: Back to state: {}", cycle_num, label));
            self.post_after_lasso(&actual, Some((lasso.cycle_pos, back_label)));
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


/// does Java throw an `EvalException` (not an `Assert.fail` `TLCRuntimeException`) for this error?  (the TLC modules do)
fn is_eval_exception(code: i32) -> bool {
    matches!(
        code,
        ec::TLC_MODULE_ARGUMENT_ERROR
            | ec::TLC_MODULE_ARGUMENT_ERROR_AN
            | ec::TLC_MODULE_ONE_ARGUMENT_ERROR
            | ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE
            | ec::TLC_MODULE_OVERFLOW
            | ec::TLC_MODULE_TLCGET_UNDEFINED
            | ec::TLC_MODULE_COMPARE_VALUE
            | ec::TLC_MODULE_CHECK_MEMBER_OF
            | ec::TLC_MODULE_TRANSITIVE_CLOSURE
    )
}

/// Java: `MP` text of `EC.SYSTEM_STACK_OVERFLOW`
const STACK_OVERFLOW_TEXT: &str = "This was a Java StackOverflowError. It was probably the result\nof an incorrect recursive function definition that caused TLC to enter\nan infinite loop when trying to compute the function or its application\nto an element in its putative domain.";

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
        live_gen_len: Vec::new(),
        live_edge: Vec::new(),
        live_inits: Vec::new(),
        fp_index: HashMap::new(),
        fmt_exc: None,
        proc_log: Vec::new(),
        init_fail: None,
        no_summary: false,
        cur_head: None,
        uses_random: tlc_core::natives::random_used(),
        outdeg_on_exit: false,
        stats_done: false,
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
            // Java: ModelChecker.modelCheckImpl: the checking has been completed, check the postconditions
            if let Some(code) = ck.check_postconditions(&setup) {
                // Java: `printSummary(false, ..)` after the error
                ck.stats(0);
                return finish(ck.rep, start, code);
            }
            ck.rep.info(
                ec::TLC_SUCCESS,
                "Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = 0.0",
            );
            ck.stats(0);
            ck.outdegree_stats();
            finish(ck.rep, start, 0)
        }
        Err(Stop::Exit(code)) => {
            if let (Some(n), false) = (ck.init_fail, ck.no_summary) {
                ck.generated = n;
                ck.max_level = if n > 0 { 1 } else { 0 };
                let left = ck.states.len();
                ck.stats(left);
            }
            // Java: the failure ended the exploration of the state being expanded: `printSummary(false, ..)`
            if !ck.stats_done && !ck.no_summary {
                if let Some(h) = ck.cur_head {
                    let left = ck.states.len().saturating_sub(h + 1);
                    ck.stats(left);
                }
            }
            if ck.outdeg_on_exit {
                ck.outdegree_stats();
            }
            finish(ck.rep, start, code)
        }
    }
}
