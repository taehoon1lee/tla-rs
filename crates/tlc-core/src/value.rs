//! Port of `tlc2.value.impl.*` (Value hierarchy): values, comparison (`compareTo`), equality, membership,
//! enumeration, printing (`toString`) and canonical hashing (fingerprints).
//!
//! Representation choices (observable behaviour is what TLC does):
//! * strings and model values are interned ids; they order by id (`UniqueString.compareTo`);
//! * a set is a sorted, duplicate-free vector (`SetEnumValue` after `normalize`), intervals/powersets/function
//!   sets stay lazy (`IntervalValue`, `SubsetValue`, `SetOfFcnsValue`, ...);
//! * functions with domain `1..n` are tuples; records are functions whose domain consists of strings;
//! * lazily evaluated functions (`FcnLambdaValue`) and filtered sets (`SetPredValue`) hold evaluator closures.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::Write as _;
use std::rc::Rc;
use tla_sany::intern;

// ---------------------------------------------------------------------------------------------- errors

/// An evaluation failure: TLC error code + message (`Assert.fail`, `EvalException`).
#[derive(Debug, Clone)]
pub struct TlcErr {
    pub code: i32,
    pub msg: String,
    /// feature not ported yet (reported as code 9999)
    pub not_ported: bool,
    /// additional context lines (TLC prints the location chain of nested evaluations)
    pub trail: Vec<String>,
    /// Java: the failure happened inside a method of a value that has a source (`Value.member`, ...), which rethrows it as a
    /// `FingerprintException` (`FingerprintException.getNewHead`) instead of letting the original exception through
    pub fp_exc: bool,
    /// Java: `CallStackTool`: the nodes (by address, innermost first) whose evaluation the failure passed on its way out
    pub frames: Vec<usize>,
    /// the failure was raised while an argument was evaluated, not by the Java method of an override: it is not wrapped by it
    pub pass: bool,
}

impl TlcErr {
    /// Java: `getMessage()` of the exception: an error built from an EC code (`MP.getMessage`) carries the tool-mode markers
    pub fn java_message(&self) -> String {
        if self.code == crate::ec::GENERAL || self.code < 0 || self.msg.starts_with("@!@!@STARTMSG") {
            self.msg.clone()
        } else {
            format!("@!@!@STARTMSG {}:0 @!@!@\n{}\n@!@!@ENDMSG {} @!@!@", self.code, self.msg, self.code)
        }
    }
}

pub type R<T> = Result<T, Box<TlcErr>>;

pub fn fail_code<T>(code: i32, msg: impl Into<String>) -> R<T> {
    Err(Box::new(TlcErr { code, msg: msg.into(), not_ported: false, trail: vec![], fp_exc: false, frames: vec![], pass: false }))
}

/// `Assert.fail(msg)` -> EC.GENERAL
pub fn fail<T>(msg: impl Into<String>) -> R<T> {
    fail_code(crate::ec::GENERAL, msg)
}

pub fn not_ported<T>(what: impl Into<String>) -> R<T> {
    Err(Box::new(TlcErr { code: crate::mp::NOT_PORTED, msg: what.into(), not_ported: true, trail: vec![], fp_exc: false, frames: vec![], pass: false }))
}

// ---------------------------------------------------------------------------------------------- values

pub struct Fcn {
    /// sorted domain (never a `1..n` integer domain: those are tuples)
    pub dom: Rc<Vec<Value>>,
    pub vals: Vec<Value>,
    /// memo of the fingerprint of this (immutable) function; 0 = not computed yet
    pub fp: std::cell::Cell<u64>,
    /// memo: no lazily evaluated component remains (`needs_normalize` is false)
    pub norm_ok: std::cell::Cell<bool>,
    /// memo of `symmetry::contains_model`: 0 = not computed, 1 = no model value inside, 2 = some
    pub has_model: std::cell::Cell<u8>,
}

impl Fcn {
    pub fn new(dom: Rc<Vec<Value>>, vals: Vec<Value>) -> Fcn {
        Fcn { dom, vals, fp: std::cell::Cell::new(0), norm_ok: std::cell::Cell::new(false), has_model: std::cell::Cell::new(0) }
    }
}

pub struct SetPred {
    pub base: Value,
    pub pred: Box<dyn Fn(&Value) -> R<bool>>,
    pub cache: RefCell<Option<Rc<Vec<Value>>>>,
}

pub struct FcnLam {
    pub dom: Value,
    pub apply: Box<dyn Fn(&Value) -> R<Value>>,
    pub cache: RefCell<Option<Value>>,
    /// the evaluator's view of the function body (`eval::LamIr`), used to expand it while enumerating actions
    pub body: Option<Rc<dyn std::any::Any>>,
}

#[derive(Clone)]
pub enum Value {
    Bool(bool),
    Int(i32),
    Str(u32),
    Model(u32),
    /// normalized finite set
    Set(Rc<Vec<Value>>),
    Interval(i32, i32),
    Tuple(Rc<Vec<Value>>),
    Fcn(Rc<Fcn>),
    SetPred(Rc<SetPred>),
    FcnLam(Rc<FcnLam>),
    Subset(Rc<Value>),
    /// a set enumeration that was not normalized because its elements cannot be compared (Java's unnormalized `SetEnumValue`)
    SetU(Rc<Vec<Value>>),
    /// `FiniteSetsExt!kSubset(k, S)`: Java's `KSubsetValue`
    KSubset(Rc<(i32, Value)>),
    SetOfFcns(Rc<(Value, Value)>),
    SetOfRcds(Rc<Vec<(u32, Value)>>),
    SetOfTuples(Rc<Vec<Value>>),
    SetCup(Rc<(Value, Value)>),
    SetCap(Rc<(Value, Value)>),
    SetDiff(Rc<(Value, Value)>),
    BigUnion(Rc<Value>),
    /// `Seq(S)`
    SeqOf(Rc<Value>),
    NatSet,
    IntSet,
    RealSet,
    StringSet,
    /// value of a variable that is not (yet) assigned in a state
    Undef,
}

/// The subsets of the normalized set `base` in the normalized order of sets (by size, then lexicographically by element),
/// generated directly without sorting 2^n sets.  `f` returns `Ok(false)` to stop (the result is `Ok(false)` then).
fn each_subset(base: &[Value], f: &mut dyn FnMut(Value) -> R<bool>) -> R<bool> {
    let n = base.len();
    for k in 0..=n {
        let mut idx: Vec<usize> = (0..k).collect();
        loop {
            if !f(Value::Set(Rc::new(idx.iter().map(|&i| base[i].clone()).collect())))? {
                return Ok(false);
            }
            // next combination in lexicographic order
            let mut j = k;
            while j > 0 && idx[j - 1] == n - k + j - 1 {
                j -= 1;
            }
            if j == 0 {
                break;
            }
            idx[j - 1] += 1;
            for t in j..k {
                idx[t] = idx[t - 1] + 1;
            }
        }
    }
    Ok(true)
}

pub const TRUE: Value = Value::Bool(true);
pub const FALSE: Value = Value::Bool(false);

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_tla())
    }
}

fn kind_name(v: &Value) -> &'static str {
    match v {
        Value::Bool(_) => "boolean",
        Value::Int(_) => "integer",
        Value::Str(_) => "string",
        Value::Model(_) => "model value",
        Value::Tuple(_) => "tuple",
        Value::Fcn(_) | Value::FcnLam(_) => "function",
        _ => "set",
    }
}

impl Value {
    pub fn str(s: &str) -> Value {
        Value::Str(intern::intern(s))
    }
    pub fn tuple(v: Vec<Value>) -> Value {
        Value::Tuple(Rc::new(v))
    }
    pub fn empty_set() -> Value {
        Value::Set(Rc::new(vec![]))
    }

    pub fn is_set_like(&self) -> bool {
        matches!(
            self,
            Value::Set(_)
                | Value::Interval(..)
                | Value::SetPred(_)
                | Value::Subset(_)
                | Value::SetU(_)
                | Value::KSubset(_)
                | Value::SetOfFcns(_)
                | Value::SetOfRcds(_)
                | Value::SetOfTuples(_)
                | Value::SetCup(_)
                | Value::SetCap(_)
                | Value::SetDiff(_)
                | Value::BigUnion(_)
                | Value::SeqOf(_)
                | Value::NatSet
                | Value::IntSet
                | Value::RealSet
                | Value::StringSet
        )
    }

    pub fn is_fcn_like(&self) -> bool {
        matches!(self, Value::Tuple(_) | Value::Fcn(_) | Value::FcnLam(_))
    }

    pub fn as_bool(&self) -> R<bool> {
        match self {
            Value::Bool(b) => Ok(*b),
            v => fail(format!("A non-boolean expression ({}) was used where a boolean was expected.", v.to_tla())),
        }
    }

    pub fn as_int(&self) -> R<i32> {
        match self {
            Value::Int(i) => Ok(*i),
            v => fail(format!("Attempted to apply an integer operation to the non-integer value\n{}", v.to_tla())),
        }
    }

    // ------------------------------------------------------------------ construction helpers

    /// build a normalized set from arbitrary elements (sort + dedup); errors on incomparable elements
    pub fn set_from(mut elems: Vec<Value>) -> R<Value> {
        if elems.len() > 1 {
            let mut err: Option<Box<TlcErr>> = None;
            elems.sort_by(|a, b| match a.cmp_val(b) {
                Ok(o) => o,
                Err(e) => {
                    if err.is_none() {
                        err = Some(e);
                    }
                    Ordering::Equal
                }
            });
            if let Some(e) = err {
                return Err(e);
            }
            let mut out: Vec<Value> = Vec::with_capacity(elems.len());
            for e in elems {
                if let Some(last) = out.last() {
                    if last.cmp_val(&e)? == Ordering::Equal {
                        continue;
                    }
                }
                out.push(e);
            }
            elems = out;
        }
        Ok(Value::Set(Rc::new(elems)))
    }

    /// build a function value from (domain element, value) pairs
    pub fn fcn_from(mut pairs: Vec<(Value, Value)>) -> R<Value> {
        if pairs.is_empty() {
            return Ok(Value::tuple(vec![]));
        }
        let mut err: Option<Box<TlcErr>> = None;
        pairs.sort_by(|a, b| match a.0.cmp_val(&b.0) {
            Ok(o) => o,
            Err(e) => {
                if err.is_none() {
                    err = Some(e);
                }
                Ordering::Equal
            }
        });
        if let Some(e) = err {
            return Err(e);
        }
        // duplicate domain elements keep... TLC rejects duplicates in function construction; keep the last
        let mut dom: Vec<Value> = Vec::with_capacity(pairs.len());
        let mut vals: Vec<Value> = Vec::with_capacity(pairs.len());
        for (d, v) in pairs {
            if let Some(last) = dom.last() {
                if last.cmp_val(&d)? == Ordering::Equal {
                    *vals.last_mut().unwrap() = v;
                    continue;
                }
            }
            dom.push(d);
            vals.push(v);
        }
        Ok(Value::fcn_sorted(dom, vals))
    }

    /// from an already sorted, duplicate-free domain
    pub fn fcn_sorted(dom: Vec<Value>, vals: Vec<Value>) -> Value {
        // domain 1..n -> tuple
        let n = dom.len();
        let mut is_seq = true;
        for (i, d) in dom.iter().enumerate() {
            match d {
                Value::Int(k) if *k as usize == i + 1 && *k >= 1 => {}
                _ => {
                    is_seq = false;
                    break;
                }
            }
        }
        if is_seq || n == 0 {
            Value::Tuple(Rc::new(vals))
        } else {
            Value::Fcn(Rc::new(Fcn::new(Rc::new(dom), vals)))
        }
    }

    pub fn record(fields: Vec<(u32, Value)>) -> Value {
        let mut f = fields;
        f.sort_by_key(|x| x.0);
        let dom: Vec<Value> = f.iter().map(|x| Value::Str(x.0)).collect();
        let vals: Vec<Value> = f.into_iter().map(|x| x.1).collect();
        Value::fcn_sorted(dom, vals)
    }

    // ------------------------------------------------------------------ forcing lazy values

    /// materialize a lazily evaluated function (`FcnLambdaValue.toFcnRcd`)
    pub fn force_fcn(&self) -> R<Value> {
        match self {
            Value::FcnLam(l) => {
                if let Some(v) = &*l.cache.borrow() {
                    return Ok(v.clone());
                }
                let elems = l.dom.enumerate()?;
                let mut dom = Vec::with_capacity(elems.len());
                let mut vals = Vec::with_capacity(elems.len());
                for e in elems.iter() {
                    vals.push((l.apply)(e)?);
                    dom.push(e.clone());
                }
                let v = Value::fcn_sorted(dom, vals);
                *l.cache.borrow_mut() = Some(v.clone());
                Ok(v)
            }
            v => Ok(v.clone()),
        }
    }

    /// Visit the elements of a set-like value in normalized order, stopping when `f` returns `Ok(false)` (the result is
    /// `Ok(false)` exactly then).  `SUBSET S` is generated element by element: Java's `SubsetValue.elements(NORMALIZED)` is
    /// lazy, so `\E s \in SUBSET S : Q` stops at the first witness.  Every other set is converted first, like
    /// `EnumerableValue.elements(NORMALIZED)` does (`toSetEnum`): in particular `{x \in S : P(x)}` evaluates `P` for ALL
    /// elements before the first one is visited (an error behind the witness is still raised).
    pub fn try_each(&self, f: &mut dyn FnMut(&Value) -> R<bool>) -> R<bool> {
        match self {
            Value::Subset(s) => {
                let base = s.enumerate()?;
                let n = base.len();
                if n >= 31 {
                    return fail(format!("Attempted to enumerate SUBSET of a set with {} elements.", n));
                }
                each_subset(&base, &mut |sv| f(&sv))
            }
            Value::Interval(lo, hi) => {
                let mut k = *lo;
                while k <= *hi {
                    if !f(&Value::Int(k))? {
                        return Ok(false);
                    }
                    if k == i32::MAX {
                        break;
                    }
                    k += 1;
                }
                Ok(true)
            }
            _ => {
                let elems = self.enumerate()?;
                for e in elems.iter() {
                    if !f(e)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }

    /// normalized element list of a finite set-like value
    pub fn enumerate(&self) -> R<Rc<Vec<Value>>> {
        match self {
            Value::Set(v) => Ok(v.clone()),
            Value::Interval(lo, hi) => {
                if hi < lo {
                    return Ok(Rc::new(vec![]));
                }
                Ok(Rc::new((*lo..=*hi).map(Value::Int).collect()))
            }
            Value::SetPred(p) => {
                if let Some(c) = &*p.cache.borrow() {
                    return Ok(c.clone());
                }
                // Java: SetPredValue.toSetEnum walks `inVal.elements()`; a SUBSET base is generated lazily there
                let mut out = Vec::new();
                p.base.try_each(&mut |e| {
                    if (p.pred)(e)? {
                        out.push(e.clone());
                    }
                    Ok(true)
                })?;
                let r = Rc::new(out);
                *p.cache.borrow_mut() = Some(r.clone());
                Ok(r)
            }
            Value::Subset(s) => {
                let base = s.enumerate()?;
                let n = base.len();
                if n >= 31 {
                    return fail_code(crate::ec::TLC_MODULE_OVERFLOW, format!("Overflow when computing the number of elements in:\n{}", crate::pprint::ppr(&self.to_tla())));
                }
                let mut out = Vec::with_capacity(1usize << n);
                each_subset(&base, &mut |sv| {
                    out.push(sv);
                    Ok(true)
                })?;
                Ok(Rc::new(out))
            }
            Value::KSubset(_) => self.ksub_enumerate(),
            // Java: SetEnumValue.normalize: the elements are compared only now
            Value::SetU(v) => match Value::set_from(v.to_vec())? {
                Value::Set(rc) => Ok(rc),
                _ => Ok(Rc::new(vec![])),
            },
            Value::SetOfFcns(p) => {
                if self.is_empty_set()? {
                    return Ok(Rc::new(vec![]));
                }
                if p.0.is_empty_set()? {
                    return Ok(Rc::new(vec![Value::tuple(vec![])]));
                }
                let doms = p.0.enumerate()?;
                let rng = p.1.enumerate()?;
                let (nd, nr) = (doms.len(), rng.len());
                let total = (nr as f64).powi(nd as i32);
                if total > 50_000_000.0 {
                    return fail("Attempted to enumerate a huge set of functions.");
                }
                let mut out = Vec::new();
                if nd == 0 {
                    out.push(Value::tuple(vec![]));
                } else if nr > 0 {
                    let mut idx = vec![0usize; nd];
                    loop {
                        let vals: Vec<Value> = idx.iter().map(|&i| rng[i].clone()).collect();
                        out.push(Value::fcn_sorted(doms.to_vec(), vals));
                        let mut k = nd;
                        loop {
                            if k == 0 {
                                break;
                            }
                            k -= 1;
                            idx[k] += 1;
                            if idx[k] < nr {
                                break;
                            }
                            idx[k] = 0;
                            if k == 0 {
                                k = usize::MAX;
                                break;
                            }
                        }
                        if k == usize::MAX {
                            break;
                        }
                    }
                }
                Ok(Value::set_from(out)?.enumerate()?)
            }
            Value::SetOfRcds(fs) => {
                if self.is_empty_set()? {
                    return Ok(Rc::new(vec![]));
                }
                let mut sets: Vec<(u32, Rc<Vec<Value>>)> = vec![];
                for (n, s) in fs.iter() {
                    sets.push((*n, s.enumerate()?));
                }
                sets.sort_by_key(|x| x.0);
                let mut out: Vec<Vec<(u32, Value)>> = vec![vec![]];
                for (n, s) in &sets {
                    let mut next = Vec::new();
                    for pre in &out {
                        for e in s.iter() {
                            let mut p = pre.clone();
                            p.push((*n, e.clone()));
                            next.push(p);
                        }
                    }
                    out = next;
                }
                let vals: Vec<Value> = out.into_iter().map(Value::record).collect();
                Ok(Value::set_from(vals)?.enumerate()?)
            }
            Value::SetOfTuples(ss) => {
                if self.is_empty_set()? {
                    return Ok(Rc::new(vec![]));
                }
                let mut sets = vec![];
                for s in ss.iter() {
                    sets.push(s.enumerate()?);
                }
                let mut out: Vec<Vec<Value>> = vec![vec![]];
                for s in &sets {
                    let mut next = Vec::new();
                    for pre in &out {
                        for e in s.iter() {
                            let mut p = pre.clone();
                            p.push(e.clone());
                            next.push(p);
                        }
                    }
                    out = next;
                }
                let vals: Vec<Value> = out.into_iter().map(Value::tuple).collect();
                Ok(Value::set_from(vals)?.enumerate()?)
            }
            Value::SetCup(p) => {
                let mut a = p.0.enumerate()?.to_vec();
                a.extend(p.1.enumerate()?.iter().cloned());
                Ok(Value::set_from(a)?.enumerate()?)
            }
            Value::SetCap(p) => {
                // Java: SetCapValue: the elements come from the operand that TLC can enumerate (`Nat \cap {1, 2}`)
                let (src, other) = if !p.0.is_finite() && p.1.is_finite() { (&p.1, &p.0) } else { (&p.0, &p.1) };
                let a = src.enumerate()?;
                let mut out = vec![];
                for e in a.iter() {
                    if other.member(e)? {
                        out.push(e.clone());
                    }
                }
                Ok(Rc::new(out))
            }
            Value::SetDiff(p) => {
                // Java: SetDiffValue.elements
                if !p.0.is_finite() {
                    return fail(format!("Attempted to enumerate S \\ T when S:\n{}\nis not enumerable.", crate::pprint::ppr(&p.0.to_tla())));
                }
                let a = p.0.enumerate()?;
                let mut out = vec![];
                for e in a.iter() {
                    if !p.1.member(e)? {
                        out.push(e.clone());
                    }
                }
                Ok(Rc::new(out))
            }
            Value::BigUnion(s) => {
                let outer = s.enumerate()?;
                let mut all = vec![];
                for e in outer.iter() {
                    if !e.is_set_like() {
                        return fail(format!(
                            "Attempted to compute UNION of a set one of whose elements is not a set:\n{}",
                            e.to_tla()
                        ));
                    }
                    all.extend(e.enumerate()?.iter().cloned());
                }
                Ok(Value::set_from(all)?.enumerate()?)
            }
            Value::SeqOf(b) if b.is_finite() && b.is_empty_set().unwrap_or(false) => Ok(Rc::new(vec![Value::tuple(vec![])])),
            Value::SeqOf(_) => fail("Attempted to enumerate the infinite set Seq(S)."),
            Value::NatSet => fail("Attempted to enumerate the infinite set Nat."),
            Value::IntSet => fail("Attempted to enumerate the infinite set Int."),
            Value::RealSet => fail("Attempted to enumerate the infinite set Real."),
            Value::StringSet => fail("Attempted to enumerate the infinite set STRING."),
            v => fail(format!("Attempted to enumerate the non-set value\n{}", v.to_tla())),
        }
    }

    /// is the set-like value finite (without enumerating it)
    pub fn is_finite(&self) -> bool {
        match self {
            Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet => false,
            // Java: SeqSetValue.isFinite: only Seq({}) = {<<>>} is finite
            Value::SeqOf(b) => b.is_finite() && b.is_empty_set().unwrap_or(false),
            Value::SetPred(p) => p.base.is_finite(),
            Value::SetCup(p) => p.0.is_finite() && p.1.is_finite(),
            Value::SetCap(p) => p.0.is_finite() || p.1.is_finite(),
            Value::SetDiff(p) => p.0.is_finite(),
            Value::Subset(s) => s.is_finite(),
            // Java: KSubsetValue.isFinite
            Value::KSubset(p) => p.0 <= 0 || p.1.is_finite(),
            // Java: SetOfFcnsValue.isFinite: an empty domain or range makes the set finite whatever the other one is
            // (isEmpty is only asked of an argument that is finite: an undecidable emptiness would fail instead of answering)
            Value::SetOfFcns(p) => {
                let (fd, fr) = (p.0.is_finite(), p.1.is_finite());
                if fd && p.0.is_empty_set().unwrap_or(false) {
                    return true;
                }
                if fr && p.1.is_empty_set().unwrap_or(false) {
                    return true;
                }
                if fd && fr {
                    return true;
                }
                fr && p.1.size().map_or(false, |n| n == 1)
            }
            // Java: SetOfRcdsValue.isFinite: an empty field makes the record set empty
            Value::SetOfRcds(fs) => {
                let mut all = true;
                for (_, s) in fs.iter() {
                    if s.is_finite() {
                        if s.is_empty_set().unwrap_or(false) {
                            return true;
                        }
                    } else {
                        all = false;
                    }
                }
                all
            }
            Value::SetOfTuples(ss) => {
                let mut all = true;
                for s in ss.iter() {
                    if s.is_finite() {
                        if s.is_empty_set().unwrap_or(false) {
                            return true;
                        }
                    } else {
                        all = false;
                    }
                }
                all
            }
            Value::BigUnion(s) => s.is_finite(),
            _ => true,
        }
    }

    /// Java: `EnumerableValue.isEmpty`: does the set have no element?  Products ask their constituents in order and stop at the first
    /// empty one; an emptiness TLC cannot decide (`Nat \ {0}`) fails.
    pub fn is_empty_set(&self) -> R<bool> {
        match self {
            Value::Set(v) => Ok(v.is_empty()),
            Value::Interval(lo, hi) => Ok(hi < lo),
            // Naturals answers the emptiness of its sets without enumerating them
            Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet | Value::SeqOf(_) => Ok(false),
            Value::Subset(_) => Ok(false),
            Value::KSubset(_) => self.ksub_no_elements(),
            Value::SetU(v) => Ok(v.is_empty()),
            Value::SetOfFcns(p) => {
                if p.0.is_empty_set()? {
                    return Ok(false);
                }
                p.1.is_empty_set()
            }
            Value::SetOfRcds(fs) => {
                for (_, s) in fs.iter() {
                    if s.is_empty_set()? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Value::SetOfTuples(ss) => {
                for s in ss.iter() {
                    if s.is_empty_set()? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            // Java: `UnionValue.isEmpty`: the first element of the union decides, the rest is not enumerated
            Value::BigUnion(s) => {
                for x in s.enumerate()?.iter() {
                    if !x.is_set_like() {
                        return fail(format!(
                            "Attempted to compute UNION of a set one of whose elements is not a set:\n{}",
                            x.to_tla()
                        ));
                    }
                    if !x.is_empty_set()? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            v if v.is_set_like() => Ok(v.enumerate()?.is_empty()),
            // Java: Value.isEmpty
            v => fail(format!("Shouldn't call isEmpty() on value {}", crate::pprint::ppr(&v.to_tla()))),
        }
    }

    /// cardinality of a finite set
    pub fn size(&self) -> R<usize> {
        match self {
            Value::Set(v) => Ok(v.len()),
            Value::Interval(lo, hi) => Ok(if hi < lo { 0 } else { (*hi as i64 - *lo as i64 + 1) as usize }),
            Value::Subset(s) => {
                let n = s.size()?;
                if n >= 31 {
                    return fail_code(crate::ec::TLC_MODULE_OVERFLOW, format!("Overflow when computing the number of elements in:\n{}", crate::pprint::ppr(&self.to_tla())));
                }
                Ok(1usize << n)
            }
            Value::KSubset(_) => self.ksub_size(),
            Value::SetOfFcns(p) => {
                // Java: SetOfFcnsValue.size: the domain is asked first, then the range
                if p.0.is_empty_set()? {
                    return Ok(1);
                }
                if p.1.is_empty_set()? {
                    return Ok(0);
                }
                let nr = p.1.size()?;
                if nr == 1 {
                    return Ok(1);
                }
                let nd = p.0.size()?;
                let mut sz: usize = 1;
                for _ in 0..nd {
                    sz = match sz.checked_mul(nr) {
                        Some(x) if x <= i32::MAX as usize => x,
                        _ => return fail(format!("Overflow when computing the number of elements in:\n{}", crate::pprint::ppr(&self.to_tla()))),
                    };
                }
                Ok(sz)
            }
            Value::SetOfRcds(fs) => {
                if self.is_empty_set()? {
                    return Ok(0);
                }
                let mut sz: usize = 1;
                for (_, s) in fs.iter() {
                    sz = sz.saturating_mul(s.size()?);
                }
                Ok(sz)
            }
            Value::SetOfTuples(ss) => {
                if self.is_empty_set()? {
                    return Ok(0);
                }
                let mut sz: usize = 1;
                for s in ss.iter() {
                    sz = sz.saturating_mul(s.size()?);
                }
                Ok(sz)
            }
            Value::SeqOf(b) if b.is_finite() && b.is_empty_set().unwrap_or(false) => Ok(1),
            Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet | Value::SeqOf(_) => {
                fail(format!("Attempted to compute the number of elements in the non-enumerable set\n{}", self.to_tla()))
            }
            v if v.is_set_like() => Ok(v.enumerate()?.len()),
            v => fail(format!("Attempted to compute the number of elements in the non-set value\n{}", v.to_tla())),
        }
    }

    // ------------------------------------------------------------------ membership

    /// `e \in self`; a failure inside a set built from the specification is a `FingerprintException` in Java
    #[inline]
    pub fn member(&self, e: &Value) -> R<bool> {
        match self.member_impl(e) {
            Err(mut err) if !matches!(self, Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet) => {
                err.fp_exc = true;
                Err(err)
            }
            r => r,
        }
    }

    fn member_impl(&self, e: &Value) -> R<bool> {
        match self {
            Value::Set(v) => {
                // binary search with the total order; errors on incomparable elements
                if v.is_empty() {
                    return Ok(false);
                }
                let (mut lo, mut hi) = (0usize, v.len());
                while lo < hi {
                    let mid = (lo + hi) / 2;
                    let ord = match (&v[mid], e) {
                        (Value::Int(a), Value::Int(b)) => a.cmp(b),
                        // Java: `elem.compareTo(elementData[mid])`: the element is the receiver of the failing comparison
                        (a, _) => match a.cmp_val(e) {
                            Ok(o) => o,
                            Err(_) => {
                                return match e.cmp_val(a) {
                                    Err(err) => Err(err),
                                    Ok(_) => linear_member(v, e),
                                }
                            }
                        },
                    };
                    match ord {
                        Ordering::Less => lo = mid + 1,
                        Ordering::Greater => hi = mid,
                        Ordering::Equal => return Ok(true),
                    }
                }
                Ok(false)
            }
            Value::Interval(lo, hi) => match e {
                Value::Int(i) => Ok(*lo <= *i && *i <= *hi),
                Value::Model(_) => Ok(false),
                // Java: IntervalValue.member: an empty interval contains nothing, whatever the element
                _ if *lo > *hi => Ok(false),
                _ => fail(format!(
                    "Attempted to check if the value:\n{}\nis in the integer interval {}",
                    e.to_tla(),
                    self.to_tla()
                )),
            },
            Value::NatSet => match e {
                Value::Int(i) => Ok(*i >= 0),
                Value::Model(_) => Ok(false),
                _ => fail_code(
                    crate::ec::TLC_MODULE_CHECK_MEMBER_OF,
                    format!("Attempted to check if the value:\n{}\nis an element of Nat.", crate::pprint::ppr(&e.to_tla())),
                ),
            },
            Value::IntSet => match e {
                Value::Int(_) => Ok(true),
                Value::Model(_) => Ok(false),
                _ => fail_code(
                    crate::ec::TLC_MODULE_CHECK_MEMBER_OF,
                    format!("Attempted to check if the value:\n{}\nis an element of Int.", crate::pprint::ppr(&e.to_tla())),
                ),
            },
            Value::RealSet => match e {
                Value::Int(_) => Ok(true),
                Value::Model(_) => Ok(false),
                _ => fail(format!("Attempted to check if the non-number value:\n{}\nis in Real.", e.to_tla())),
            },
            Value::StringSet => match e {
                Value::Str(_) => Ok(true),
                Value::Model(_) => Ok(false),
                _ => Ok(false),
            },
            Value::SetPred(p) => {
                if !p.base.member(e)? {
                    return Ok(false);
                }
                (p.pred)(e)
            }
            Value::Subset(s) => {
                if !e.is_set_like() {
                    e.check_printable()?;
                    self.check_printable()?;
                    return fail(format!("Attempted to check if the non-enumerable value\n{}\nis element of\n{}", crate::pprint::ppr(&e.to_tla()), crate::pprint::ppr(&self.to_tla())));
                }
                e.subseteq(s)
            }
            // Java: KSubsetValue.member: the size is asked first, then every element has to be in the base set
            Value::SetU(v) => linear_member(v, e),
            Value::KSubset(p) => {
                if self.ksub_no_elements()? {
                    return Ok(false);
                }
                if p.0 as i64 != e.size()? as i64 {
                    return Ok(false);
                }
                for x in e.enumerate()?.iter() {
                    if !p.1.member(x)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Value::SetOfFcns(p) => {
                let f = e.force_fcn()?;
                if !f.is_fcn_like() {
                    return Ok(false);
                }
                let dom = f.domain()?;
                if !dom.eq_val(&p.0)? {
                    return Ok(false);
                }
                // the values are borrowed: this is called for every membership test of a (nested) record/function set
                let vals: &[Value] = match &f {
                    Value::Tuple(t) => t,
                    Value::Fcn(fc) => &fc.vals,
                    v => return fail(format!("Attempted to get the range of the non-function
{}", v.to_tla())),
                };
                for v in vals.iter() {
                    if !p.1.member(v)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Value::SetOfRcds(fs) => {
                let f = e.force_fcn()?;
                match &f {
                    Value::Fcn(fc) => {
                        if fc.dom.len() != fs.len() {
                            return Ok(false);
                        }
                        if fc.dom.iter().any(|d| !matches!(d, Value::Str(_))) {
                            return self.non_record_member(e);
                        }
                        for (d, v) in fc.dom.iter().zip(fc.vals.iter()) {
                            match d {
                                Value::Str(id) => match fs.iter().find(|(n, _)| n == id) {
                                    Some((_, s)) => {
                                        if !s.member(v)? {
                                            return Ok(false);
                                        }
                                    }
                                    None => return Ok(false),
                                },
                                _ => return Ok(false),
                            }
                        }
                        Ok(true)
                    }
                    // a tuple has the integer domain 1..n: only the empty tuple can be a record (of no fields)
                    Value::Tuple(t) if t.is_empty() => Ok(fs.is_empty()),
                    Value::Model(_) => Ok(false),
                    _ => self.non_record_member(e),
                }
            }
            Value::SetOfTuples(ss) => match e {
                Value::Tuple(t) => {
                    if t.len() != ss.len() {
                        return Ok(false);
                    }
                    for (x, s) in t.iter().zip(ss.iter()) {
                        if !s.member(x)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                // Java: SetOfTuplesValue.member: a function with an integer domain is not a tuple of this length, any other value
                // that is not a tuple cannot be asked
                Value::Fcn(fc) => {
                    if fc.dom.iter().any(|d| !matches!(d, Value::Int(_))) {
                        return self.non_tuple_member(e);
                    }
                    Ok(false)
                }
                Value::Model(_) => Ok(false),
                _ => self.non_tuple_member(e),
            },
            Value::SeqOf(s) => {
                let f = e.force_fcn()?;
                match &f {
                    Value::Tuple(t) => {
                        for x in t.iter() {
                            if !s.member(x)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    _ => Ok(false),
                }
            }
            Value::SetCup(p) => Ok(p.0.member(e)? || p.1.member(e)?),
            Value::SetCap(p) => Ok(p.0.member(e)? && p.1.member(e)?),
            Value::SetDiff(p) => Ok(p.0.member(e)? && !p.1.member(e)?),
            Value::BigUnion(s) => {
                for x in s.enumerate()?.iter() {
                    if x.member(e)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            v => fail(format!("Attempted to check if the value:\n{}\nis an element of the non-set value\n{}", e.to_tla(), v.to_tla())),
        }
    }

    pub fn subseteq(&self, other: &Value) -> R<bool> {
        if let (Value::Interval(a, b), Value::Interval(c, d)) = (self, other) {
            return Ok(b < a || (c <= a && b <= d));
        }
        // Java: SubsetValue.isSubsetEq: (SUBSET A subseteq SUBSET B) is reduced to (A subseteq B) to avoid the exponential
        // blowup of generating the power set
        if let (Value::Subset(a), Value::Subset(b)) = (self, other) {
            if a.is_finite() {
                return a.subseteq(b);
            }
        }
        if !self.is_finite() {
            return fail(format!("Attempted to check whether the infinite set\n{}\nis a subset of another set.", self.to_tla()));
        }
        for e in self.enumerate()?.iter() {
            if !other.member(e)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // ------------------------------------------------------------------ functions

    /// (domain, values) of a function-like value that is not a tuple
    pub fn fcn_parts(&self) -> Option<(Vec<Value>, Vec<Value>)> {
        match self {
            Value::Fcn(f) => Some((f.dom.to_vec(), f.vals.clone())),
            Value::Tuple(t) => Some(((1..=t.len() as i32).map(Value::Int).collect(), t.to_vec())),
            _ => None,
        }
    }

    pub fn fcn_values(&self) -> R<Vec<Value>> {
        match self.force_fcn()? {
            Value::Tuple(t) => Ok(t.to_vec()),
            Value::Fcn(f) => Ok(f.vals.clone()),
            v => fail(format!("Attempted to get the range of the non-function\n{}", v.to_tla())),
        }
    }

    pub fn domain(&self) -> R<Value> {
        match self {
            Value::Tuple(t) => Ok(Value::Interval(1, t.len() as i32)),
            Value::Fcn(f) => Ok(Value::Set(f.dom.clone())),
            Value::FcnLam(l) if matches!(l.dom, Value::SetU(_)) => self.force_fcn()?.domain(),
            Value::FcnLam(l) => Ok(l.dom.clone()),
            v => fail(format!("Attempted to apply the operator DOMAIN to the non-function value\n{}", v.to_tla())),
        }
    }

    /// `f[x]`
    pub fn apply(&self, arg: &Value) -> R<Value> {
        match self {
            Value::Tuple(t) => match arg {
                Value::Int(i) if *i >= 1 && (*i as usize) <= t.len() => Ok(t[*i as usize - 1].clone()),
                _ => fail(format!(
                    "Attempted to apply function:\n{}\nto argument {}, which is not in the domain of the function.",
                    self.to_tla(),
                    arg.to_tla()
                )),
            },
            Value::Fcn(f) => {
                if let Some(i) = Self::search(&f.dom, arg)? {
                    return Ok(f.vals[i].clone());
                }
                fail(format!(
                    "Attempted to apply function:\n{}\nto argument {}, which is not in the domain of the function.",
                    self.to_tla(),
                    arg.to_tla()
                ))
            }
            Value::FcnLam(l) => {
                if let Some(v) = &*l.cache.borrow() {
                    return v.apply(arg);
                }
                if !l.dom.member(arg)? {
                    // Java: FcnLambdaValue.apply
                    return fail(format!(
                        "In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n",
                        crate::pprint::ppr(&self.force_fcn()?.to_tla()),
                        crate::pprint::ppr(&arg.to_tla())
                    ));
                }
                (l.apply)(arg)
            }
            v => fail(format!("Attempted to apply the non-function\n{}\nto argument {}", v.to_tla(), arg.to_tla())),
        }
    }

    fn search(dom: &[Value], x: &Value) -> R<Option<usize>> {
        // integer and string keys (array indexes, record fields) are compared inline; dense integer domains are indexed
        match x {
            Value::Int(k) => {
                if let Some(Value::Int(d0)) = dom.first() {
                    let idx = (*k as i64) - (*d0 as i64);
                    if idx >= 0 && (idx as usize) < dom.len() {
                        if let Value::Int(d) = &dom[idx as usize] {
                            if d == k {
                                return Ok(Some(idx as usize));
                            }
                        }
                    }
                }
                let (mut lo, mut hi) = (0usize, dom.len());
                while lo < hi {
                    let mid = (lo + hi) / 2;
                    let ord = match &dom[mid] {
                        Value::Int(d) => d.cmp(k),
                        other => other.cmp_val(x)?,
                    };
                    match ord {
                        Ordering::Less => lo = mid + 1,
                        Ordering::Greater => hi = mid,
                        Ordering::Equal => return Ok(Some(mid)),
                    }
                }
                return Ok(None);
            }
            Value::Str(k) => {
                let (mut lo, mut hi) = (0usize, dom.len());
                while lo < hi {
                    let mid = (lo + hi) / 2;
                    let ord = match &dom[mid] {
                        Value::Str(d) => d.cmp(k),
                        other => other.cmp_val(x)?,
                    };
                    match ord {
                        Ordering::Less => lo = mid + 1,
                        Ordering::Greater => hi = mid,
                        Ordering::Equal => return Ok(Some(mid)),
                    }
                }
                return Ok(None);
            }
            _ => {}
        }
        let (mut lo, mut hi) = (0usize, dom.len());
        while lo < hi {
            let mid = (lo + hi) / 2;
            match dom[mid].cmp_val(x)? {
                Ordering::Less => lo = mid + 1,
                Ordering::Greater => hi = mid,
                Ordering::Equal => return Ok(Some(mid)),
            }
        }
        Ok(None)
    }

    /// `[f EXCEPT ![path] = v]` with a single path component
    pub fn except1(&self, arg: &Value, v: Value) -> R<Value> {
        match self {
            Value::Tuple(t) => match arg {
                Value::Int(i) if *i >= 1 && (*i as usize) <= t.len() => {
                    let mut n = t.to_vec();
                    n[*i as usize - 1] = v;
                    Ok(Value::tuple(n))
                }
                _ => Ok(self.clone()),
            },
            Value::Fcn(f) => match Self::search(&f.dom, arg)? {
                Some(i) => {
                    let mut vals = f.vals.clone();
                    vals[i] = v;
                    Ok(Value::Fcn(Rc::new(Fcn::new(f.dom.clone(), vals))))
                }
                None => Ok(self.clone()),
            },
            Value::FcnLam(l) if !l.dom.is_finite() || matches!(l.dom, Value::SetU(_)) => {
                // Java: FcnLambdaValue.takeExcept keeps the function lazy: the new value is one more case of the application
                if !l.dom.member(arg)? {
                    return Ok(self.clone());
                }
                let (old, at, nv) = (l.clone(), arg.clone(), v);
                Ok(Value::FcnLam(Rc::new(FcnLam {
                    dom: l.dom.clone(),
                    apply: Box::new(move |x: &Value| if x.eq_val(&at)? { Ok(nv.clone()) } else { (old.apply)(x) }),
                    cache: RefCell::new(None),
                    body: None,
                })))
            }
            Value::FcnLam(_) => self.force_fcn()?.except1(arg, v),
            _ => fail(format!("Attempted to apply EXCEPT to the non-function\n{}", self.to_tla())),
        }
    }

    // ------------------------------------------------------------------ comparison

    fn set_like_cmp_ready(&self) -> bool {
        self.is_set_like()
    }

    /// `Value.compareTo`
    /// the total order of TLC values; scalars are compared inline, everything else by `cmp_val_slow`
    #[inline]
    pub fn cmp_val(&self, o: &Value) -> R<Ordering> {
        match (self, o) {
            (Value::Int(a), Value::Int(b)) => Ok(a.cmp(b)),
            (Value::Str(a), Value::Str(b)) => Ok(a.cmp(b)),
            _ => self.cmp_val_slow(o),
        }
    }

    pub fn cmp_val_slow(&self, o: &Value) -> R<Ordering> {
        use Value::*;
        match (self, o) {
            // shared structure: identical values compare equal without looking inside
            (Set(a), Set(b)) if Rc::ptr_eq(a, b) => Ok(Ordering::Equal),
            (Tuple(a), Tuple(b)) if Rc::ptr_eq(a, b) => Ok(Ordering::Equal),
            (Fcn(a), Fcn(b)) if Rc::ptr_eq(a, b) => Ok(Ordering::Equal),
            (Int(a), Int(b)) => Ok(a.cmp(b)),
            (Str(a), Str(b)) => Ok(a.cmp(b)),
            (Bool(a), Bool(b)) => Ok(a.cmp(b)),
            // the standard infinite sets (Nat, Int, Real, STRING, Seq(S)) are ordered by kind
            (x, y) if is_std_infinite(x) && is_std_infinite(y) => match (x, y) {
                (SeqOf(p), SeqOf(q)) => p.cmp_val(q),
                _ => Ok(std_infinite_rank(x).cmp(&std_infinite_rank(y))),
            },
            // Java: ModelValue.compareTo: a typed model value (`A_x`) is comparable only with model values of the same
            // type or untyped ones
            (Model(a), Model(b)) => {
                if let (Some(x), Some(y)) = (model_type(*a), model_type(*b)) {
                    if x != y {
                        return fail(format!(
                            "Attempted to compare the differently-typed model values {} and {}",
                            intern::name_of(*a),
                            intern::name_of(*b)
                        ));
                    }
                }
                Ok(a.cmp(b))
            }
            (Model(a), o) => {
                if model_type(*a).is_some() {
                    return fail(format!("Attempted to compare the typed model value {} and non-model value\n{}", intern::name_of(*a), o.to_tla()));
                }
                Ok(Ordering::Less)
            }
            (_, Model(_)) => Ok(Ordering::Greater),
            (Tuple(a), Tuple(b)) => {
                if a.len() != b.len() {
                    return Ok(a.len().cmp(&b.len()));
                }
                for (x, y) in a.iter().zip(b.iter()) {
                    let c = x.cmp_val(y)?;
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                Ok(Ordering::Equal)
            }
            (Fcn(fa), Fcn(fb)) => {
                if !Rc::ptr_eq(&fa.dom, &fb.dom) {
                    if fa.dom.len() != fb.dom.len() {
                        return Ok(fa.dom.len().cmp(&fb.dom.len()));
                    }
                    for (x, y) in fa.dom.iter().zip(fb.dom.iter()) {
                        let c = x.cmp_val(y)?;
                        if c != Ordering::Equal {
                            return Ok(c);
                        }
                    }
                }
                for (x, y) in fa.vals.iter().zip(fb.vals.iter()) {
                    let c = x.cmp_val(y)?;
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                Ok(Ordering::Equal)
            }
            (a, b) if a.is_fcn_like() && b.is_fcn_like() => {
                let (fa, fb) = (a.force_fcn()?, b.force_fcn()?);
                let (da, va) = fa.fcn_parts().unwrap();
                let (db, vb) = fb.fcn_parts().unwrap();
                if da.len() != db.len() {
                    return Ok(da.len().cmp(&db.len()));
                }
                for (x, y) in da.iter().zip(db.iter()) {
                    let c = x.cmp_val(y)?;
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                for (x, y) in va.iter().zip(vb.iter()) {
                    let c = x.cmp_val(y)?;
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                Ok(Ordering::Equal)
            }
            // Java: KSubsetValue.compareTo, SubsetValue.compareTo (a k-subset on either side)
            (KSubset(_), b) if b.is_set_like() => self.ksub_cmp(b),
            (a, KSubset(_)) if a.is_set_like() => Ok(o.ksub_cmp(a)?.reverse()),
            (a, b) if a.set_like_cmp_ready() && b.set_like_cmp_ready() => {
                if let (Interval(a1, b1), Interval(a2, b2)) = (a, b) {
                    let (n1, n2) = (if b1 < a1 { 0 } else { *b1 as i64 - *a1 as i64 + 1 }, if b2 < a2 { 0 } else { *b2 as i64 - *a2 as i64 + 1 });
                    if n1 != n2 {
                        return Ok(n1.cmp(&n2));
                    }
                    if n1 == 0 {
                        return Ok(Ordering::Equal);
                    }
                    return Ok(a1.cmp(a2));
                }
                // an interval against an explicit set: no allocation
                if let (Interval(lo, hi), Set(v)) | (Set(v), Interval(lo, hi)) = (a, b) {
                    let n = if hi < lo { 0 } else { *hi as i64 - *lo as i64 + 1 };
                    let swapped = matches!(a, Set(_));
                    if n != v.len() as i64 {
                        let o = n.cmp(&(v.len() as i64));
                        return Ok(if swapped { o.reverse() } else { o });
                    }
                    for (i, y) in v.iter().enumerate() {
                        let c = Int(*lo + i as i32).cmp_val(y)?;
                        if c != Ordering::Equal {
                            return Ok(if swapped { c.reverse() } else { c });
                        }
                    }
                    return Ok(Ordering::Equal);
                }
                let ea = a.enumerate()?;
                let eb = b.enumerate()?;
                if ea.len() != eb.len() {
                    return Ok(ea.len().cmp(&eb.len()));
                }
                for (x, y) in ea.iter().zip(eb.iter()) {
                    let c = x.cmp_val(y)?;
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                Ok(Ordering::Equal)
            }
            // Java: IntValue / StringValue / BoolValue.compareTo
            (a @ (Int(_) | Str(_) | Bool(_)), b) => fail(format!(
                "Attempted to compare {} {} with non-{}:\n{}",
                kind_name(a),
                crate::pprint::ppr(&a.to_tla()),
                kind_name(a),
                crate::pprint::ppr(&b.to_tla())
            )),
            (a, b) => fail(format!(
                "Attempted to compare {} {} with {} {}.",
                kind_name(a),
                a.to_tla(),
                kind_name(b),
                b.to_tla()
            )),
        }
    }

    /// `Value.equals` (TLC raises an error when comparing values of different kinds)
    pub fn eq_val(&self, o: &Value) -> R<bool> {
        use Value::*;
        match (self, o) {
            (Set(a), Set(b)) if Rc::ptr_eq(a, b) => Ok(true),
            (Tuple(a), Tuple(b)) if Rc::ptr_eq(a, b) => Ok(true),
            (Fcn(a), Fcn(b)) if Rc::ptr_eq(a, b) => Ok(true),
            (Int(a), Int(b)) => Ok(a == b),
            (Str(a), Str(b)) => Ok(a == b),
            (Bool(a), Bool(b)) => Ok(a == b),
            // Java: ModelValue.equals
            (Model(a), Model(b)) => {
                if a == b {
                    return Ok(true);
                }
                if let (Some(x), Some(y)) = (model_type(*a), model_type(*b)) {
                    if x != y {
                        return fail(format!(
                            "Attempted to check equality of the differently-typed model values {} and {}",
                            intern::name_of(*a),
                            intern::name_of(*b)
                        ));
                    }
                }
                Ok(false)
            }
            (Model(a), o) => {
                if model_type(*a).is_some() {
                    return fail(format!("Attempted to check equality of typed model value {} and non-model value\n{}", intern::name_of(*a), o.to_tla()));
                }
                Ok(false)
            }
            (_, Model(_)) => Ok(false),
            (Tuple(a), Tuple(b)) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (x, y) in a.iter().zip(b.iter()) {
                    if !x.eq_val(y)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (a, b) if a.is_fcn_like() && b.is_fcn_like() => Ok(a.cmp_val(b)? == Ordering::Equal),
            (a, b) if a.is_set_like() && b.is_set_like() => {
                if let (Interval(..), Interval(..)) = (a, b) {
                    return Ok(a.cmp_val(b)? == Ordering::Equal);
                }
                // Java: KSubsetValue.equals / SubsetValue.equals / SetEnumValue.equals (converts the other value)
                if matches!(a, KSubset(_)) {
                    return a.ksub_eq(b);
                }
                if matches!(b, KSubset(_)) {
                    return b.ksub_eq(a);
                }
                if let Some(r) = set_eq_special(a, b)? {
                    return Ok(r);
                }
                if !a.is_finite() || !b.is_finite() {
                    return fail(format!(
                        "Attempted to check equality of the infinite set\n{}\nwith the value:\n{}",
                        a.to_tla(),
                        b.to_tla()
                    ));
                }
                Ok(a.cmp_val(b)? == Ordering::Equal)
            }
            // Java: IntValue / StringValue / BoolValue.equals
            (a @ (Int(_) | Str(_)), b) => fail(format!(
                "Attempted to check equality of {} {} with non-{}:\n{}",
                kind_name(a),
                crate::pprint::ppr(&a.to_tla()),
                kind_name(a),
                crate::pprint::ppr(&b.to_tla())
            )),
            (a @ Bool(_), b) => fail(format!(
                "Attempted to compare equality of boolean {} with non-boolean:\n{}",
                crate::pprint::ppr(&a.to_tla()),
                crate::pprint::ppr(&b.to_tla())
            )),
            (a, b) => fail(format!(
                "Attempted to check equality of {} {} with {} {}.",
                kind_name(a),
                a.to_tla(),
                kind_name(b),
                b.to_tla()
            )),
        }
    }

    // ------------------------------------------------------------------ printing

    /// `Value.toString()`
    pub fn to_tla(&self) -> String {
        let mut s = String::new();
        self.write_tla(&mut s);
        s
    }

    pub fn write_tla(&self, out: &mut String) {
        match self {
            Value::Bool(b) => out.push_str(if *b { "TRUE" } else { "FALSE" }),
            Value::Int(i) => {
                let _ = write!(out, "{}", i);
            }
            Value::Str(id) => {
                out.push('"');
                for c in intern::name_of(*id).chars() {
                    match c {
                        '"' => out.push_str("\\\""),
                        '\\' => out.push_str("\\\\"),
                        '\n' => out.push_str("\\n"),
                        '\t' => out.push_str("\\t"),
                        '\r' => out.push_str("\\r"),
                        '\u{c}' => out.push_str("\\f"),
                        c => out.push(c),
                    }
                }
                out.push('"');
            }
            Value::Model(id) => out.push_str(&intern::name_of(*id)),
            Value::Set(v) => {
                out.push('{');
                for (i, e) in v.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    e.write_tla(out);
                }
                out.push('}');
            }
            Value::Interval(lo, hi) => {
                if lo <= hi {
                    let _ = write!(out, "{}..{}", lo, hi);
                } else {
                    out.push_str("{}");
                }
            }
            Value::Tuple(t) => {
                out.push_str("<<");
                for (i, e) in t.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    e.write_tla(out);
                }
                out.push_str(">>");
            }
            Value::Fcn(f) => {
                let is_rcd = f.dom.iter().all(|d| matches!(d, Value::Str(_)));
                if is_rcd {
                    out.push('[');
                    for (i, (d, v)) in f.dom.iter().zip(f.vals.iter()).enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        if let Value::Str(id) = d {
                            out.push_str(&intern::name_of(*id));
                        }
                        out.push_str(" |-> ");
                        v.write_tla(out);
                    }
                    out.push(']');
                } else {
                    out.push('(');
                    for (i, (d, v)) in f.dom.iter().zip(f.vals.iter()).enumerate() {
                        if i > 0 {
                            out.push_str(" @@ ");
                        }
                        d.write_tla(out);
                        out.push_str(" :> ");
                        v.write_tla(out);
                    }
                    out.push(')');
                }
            }
            Value::FcnLam(_) => match self.force_fcn() {
                Ok(v) => v.write_tla(out),
                Err(_) => out.push_str("<function>"),
            },
            Value::Undef => out.push_str("<undefined>"),
            Value::SeqOf(s) => {
                out.push_str("Seq(");
                s.write_tla(out);
                out.push(')');
            }
            Value::NatSet => out.push_str("Nat"),
            Value::IntSet => out.push_str("Int"),
            Value::RealSet => out.push_str("Real"),
            Value::StringSet => out.push_str("STRING"),
            // Java: SubsetValue.toString: a base with fewer than 7 elements is expanded, an interval base is parenthesized
            Value::Subset(s) => match s.size() {
                Ok(n) if n < 7 => match self.enumerate() {
                    Ok(e) => Value::Set(e).write_tla(out),
                    Err(_) => out.push_str("<set>"),
                },
                _ => {
                    out.push_str("SUBSET ");
                    if matches!(**s, Value::Interval(..)) {
                        out.push('(');
                        s.write_tla(out);
                        out.push(')');
                    } else {
                        s.write_tla(out);
                    }
                }
            },
            Value::SetU(v) => {
                out.push('{');
                for (i, e) in v.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    e.write_tla(out);
                }
                out.push('}');
            }
            // Java: KSubsetValue.toString: expanded below 64 elements
            Value::KSubset(p) => match self.ksub_size() {
                Ok(n) if n < 64 => {
                    if n == 0 {
                        out.push_str("{}");
                    } else {
                        match self.ksub_enumerate() {
                            Ok(e) => Value::Set(e).write_tla(out),
                            Err(_) => out.push_str("<set>"),
                        }
                    }
                }
                _ => {
                    out.push_str("{s \\in SUBSET (");
                    p.1.write_tla(out);
                    let _ = write!(out, ") : Cardinality(s) = {}}}", p.0);
                }
            },
            Value::SetOfRcds(fs) if !self.expands() => {
                out.push('[');
                for (i, (n, s)) in fs.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&intern::name_of(*n));
                    out.push_str(": ");
                    s.write_tla(out);
                }
                out.push(']');
            }
            Value::SetOfFcns(p) if !self.expands() => {
                out.push('[');
                p.0.write_tla(out);
                out.push_str(" -> ");
                p.1.write_tla(out);
                out.push(']');
            }
            Value::SetOfTuples(ss) if !self.expands() => {
                if !ss.is_empty() {
                    out.push('(');
                }
                for (i, s) in ss.iter().enumerate() {
                    if i > 0 {
                        out.push_str(" \\X ");
                    }
                    s.write_tla(out);
                }
                if !ss.is_empty() {
                    out.push(')');
                }
            }
            v => match v.enumerate() {
                Ok(e) => Value::Set(e).write_tla(out),
                Err(_) => out.push_str("<set>"),
            },
        }
    }

    /// Java: the size test of `toString` of `SetOfRcdsValue` / `SetOfFcnsValue` / `SetOfTuplesValue` (`TLCGlobals.expand`): the number of
    /// elements, computed like Java does (an empty constituent stops the product before the others are asked); `None` for other values
    pub fn expand_size(&self) -> R<Option<u128>> {
        let product = |sizes: &mut dyn Iterator<Item = &Value>| -> R<u128> {
            let mut sz = 1u128;
            for s in sizes {
                let n = s.size()?;
                if n == 0 {
                    return Ok(0);
                }
                if sz <= 2147483647 {
                    sz *= n as u128;
                }
            }
            Ok(sz)
        };
        Ok(match self {
            Value::SetOfRcds(fs) => Some(product(&mut fs.iter().map(|(_, s)| s))?),
            Value::SetOfTuples(ss) => Some(product(&mut ss.iter())?),
            Value::SetOfFcns(p) => {
                if p.0.is_empty_set()? {
                    Some(1)
                } else {
                    let d = p.0.size()?;
                    let r = p.1.size()?;
                    Some(match (r, d) {
                        (_, 0) | (1, _) => 1,
                        (0, _) => 0,
                        _ => {
                            let mut sz = 1u128;
                            for _ in 0..d {
                                if sz > 2147483647 {
                                    break;
                                }
                                sz *= r as u128;
                            }
                            sz
                        }
                    })
                }
            }
            _ => None,
        })
    }

    /// Java: `TLCGlobals.expand` with `enumBound = 2000`: a product-like set is printed as its elements only if it has fewer
    fn expands(&self) -> bool {
        matches!(self.expand_size(), Ok(Some(n)) if n < 2000)
    }

    // ------------------------------------------------------------------ fingerprints

    /// canonical hash of a value (equal values hash equal regardless of representation)
    pub fn hash_into(&self, h: &mut Hasher) -> R<()> {
        match self {
            Value::Bool(b) => h.write_u64(if *b { 0x11 } else { 0x10 }),
            Value::Int(i) => {
                h.write_u64(0x20);
                h.write_u64(*i as i64 as u64);
            }
            Value::Str(id) => {
                h.write_u64(0x30);
                h.write_u64(str_fp_class(*id));
            }
            Value::Model(id) => {
                h.write_u64(0x40);
                h.write_u64(*id as u64);
            }
            Value::Set(v) => {
                h.write_u64(0x50);
                h.write_u64(v.len() as u64);
                for e in v.iter() {
                    e.hash_into(h)?;
                }
            }
            Value::Tuple(t) => {
                h.write_u64(0x60);
                h.write_u64(t.len() as u64);
                for e in t.iter() {
                    e.hash_into(h)?;
                }
            }
            Value::Fcn(f) => {
                // hierarchical: the hash of a function is computed once (the same `Rc` is shared by successive states)
                let mut sub = f.fp.get();
                if sub == 0 {
                    let mut hh = Hasher::new();
                    hh.write_u64(0x70);
                    hh.write_u64(f.dom.len() as u64);
                    for (d, v) in f.dom.iter().zip(f.vals.iter()) {
                        d.hash_into(&mut hh)?;
                        v.hash_into(&mut hh)?;
                    }
                    sub = hh.finish().max(1);
                    f.fp.set(sub);
                }
                h.write_u64(0x70);
                h.write_u64(sub);
            }
            Value::FcnLam(_) => self.force_fcn()?.hash_into(h)?,
            v if v.is_set_like() => {
                let e = v.enumerate()?;
                h.write_u64(0x50);
                h.write_u64(e.len() as u64);
                for x in e.iter() {
                    x.hash_into(h)?;
                }
            }
            v => return fail(format!("Attempted to fingerprint the unsupported value {}", v.to_tla())),
        }
        Ok(())
    }

    /// bring a value into canonical (fully evaluated) form so it can be stored in a state
    pub fn normalize(&self) -> R<Value> {
        match self {
            Value::FcnLam(_) => self.force_fcn()?.normalize(),
            Value::Set(v) => {
                if v.iter().any(|e| e.needs_normalize()) {
                    let mut out = Vec::with_capacity(v.len());
                    for e in v.iter() {
                        out.push(e.normalize()?);
                    }
                    Value::set_from(out)
                } else {
                    Ok(self.clone())
                }
            }
            Value::Tuple(t) => {
                if t.iter().any(|e| e.needs_normalize()) {
                    let mut out = Vec::with_capacity(t.len());
                    for e in t.iter() {
                        out.push(e.normalize()?);
                    }
                    Ok(Value::tuple(out))
                } else {
                    Ok(self.clone())
                }
            }
            Value::Fcn(f) => {
                if f.vals.iter().any(|e| e.needs_normalize()) || f.dom.iter().any(|e| e.needs_normalize()) {
                    let mut vals = Vec::with_capacity(f.vals.len());
                    for e in f.vals.iter() {
                        vals.push(e.normalize()?);
                    }
                    Ok(Value::Fcn(Rc::new(Fcn::new(f.dom.clone(), vals))))
                } else {
                    Ok(self.clone())
                }
            }
            Value::Interval(lo, hi) => Ok(if hi < lo { Value::empty_set() } else { self.clone() }),
            v if v.is_set_like() && !matches!(v, Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet | Value::SeqOf(_)) => {
                let e = v.enumerate()?;
                Value::Set(e).normalize()
            }
            v => Ok(v.clone()),
        }
    }

    /// number of elements of a (lazy) set, saturating
    fn card_sat(&self) -> u128 {
        match self {
            Value::Set(s) => s.len() as u128,
            Value::Interval(lo, hi) => {
                if hi < lo {
                    0
                } else {
                    (*hi as i64 - *lo as i64 + 1) as u128
                }
            }
            Value::Subset(b) => {
                let n = b.card_sat();
                if n >= 127 {
                    u128::MAX
                } else {
                    1u128 << n
                }
            }
            _ => 0,
        }
    }

    /// a `SUBSET S` that stays lazy when it is bound to a variable (Java keeps the `SubsetValue`, which prints as `SUBSET S`): more
    /// than 2^16 elements (the ones TLC would never enumerate are in it)
    pub fn is_huge_subset(&self) -> bool {
        matches!(self, Value::Subset(_)) && self.card_sat() > (1u128 << 16)
    }

    fn needs_normalize(&self) -> bool {
        match self {
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => false,
            Value::Set(v) => v.iter().any(|e| e.needs_normalize()),
            Value::Tuple(t) => t.iter().any(|e| e.needs_normalize()),
            Value::Fcn(f) => {
                if f.norm_ok.get() {
                    return false;
                }
                let n = f.vals.iter().any(|e| e.needs_normalize()) || f.dom.iter().any(|e| e.needs_normalize());
                if !n {
                    f.norm_ok.set(true);
                }
                n
            }
            _ => true,
        }
    }
}


// ---------------------------------------------------------------------------------------------- unnormalized set enumerations

/// Java: `SetEnumValue.member` of a set that is not normalized: the stored elements are compared with `equals`, in order
pub fn linear_member(elems: &[Value], e: &Value) -> R<bool> {
    for x in elems {
        if x.eq_val(e)? {
            return Ok(true);
        }
    }
    Ok(false)
}

impl Value {
    /// a set enumeration `{e1, ..., en}`: Java normalizes it only when it has to (to compare, enumerate or fingerprint it), so
    /// elements that cannot be compared (`{1, "a"}`) leave it unnormalized instead of failing the evaluation
    pub fn set_lit(elems: Vec<Value>) -> R<Value> {
        let simple = |k: fn(&Value) -> bool| elems.iter().all(k);
        if elems.len() < 2 || simple(|v| matches!(v, Value::Int(_))) || simple(|v| matches!(v, Value::Str(_))) || simple(|v| matches!(v, Value::Bool(_))) {
            return Value::set_from(elems);
        }
        let stored = elems.clone();
        match Value::set_from(elems) {
            Ok(v) => Ok(v),
            Err(_) => Ok(Value::SetU(Rc::new(stored))),
        }
    }

    fn non_tuple_member(&self, e: &Value) -> R<bool> {
        e.check_printable()?;
        self.check_printable()?;
        fail(format!("Attempted to check if non-tuple\n{}\nis in the set of tuples:\n{}", crate::pprint::ppr(&e.to_tla()), crate::pprint::ppr(&self.to_tla())))
    }

    fn non_record_member(&self, e: &Value) -> R<bool> {
        e.check_printable()?;
        self.check_printable()?;
        fail(format!("Attempted to check if non-record\n{}\nis in the set of records:\n{}", e.to_tla(), crate::pprint::ppr(&self.to_tla())))
    }

    /// Java: `toString` of a set enumeration normalizes it, so building an error message that shows it fails when its elements
    /// cannot be compared
    pub fn check_printable(&self) -> R<()> {
        match self {
            Value::SetU(_) => self.enumerate().map(|_| ()),
            Value::Set(v) => v.iter().try_for_each(|e| e.check_printable()),
            Value::Tuple(v) => v.iter().try_for_each(|e| e.check_printable()),
            Value::SetOfTuples(v) => v.iter().try_for_each(|e| e.check_printable()),
            Value::SetOfRcds(v) => v.iter().try_for_each(|(_, e)| e.check_printable()),
            Value::SetOfFcns(p) => {
                p.0.check_printable()?;
                p.1.check_printable()
            }
            Value::Subset(s) => s.check_printable(),
            _ => Ok(()),
        }
    }

    /// does the value hold an unnormalized set enumeration (Java normalizes it only when it fingerprints or prints the value)?
    pub fn contains_setu(&self) -> bool {
        match self {
            Value::SetU(_) => true,
            Value::Set(v) | Value::Tuple(v) => v.iter().any(|e| e.contains_setu()),
            Value::Fcn(f) => f.vals.iter().any(|e| e.contains_setu()),
            _ => false,
        }
    }

    /// the elements of an enumerated set in the order Java stores them: written order for an unnormalized set enumeration,
    /// the normalized order otherwise
    pub fn stored_elems(&self) -> R<Vec<Value>> {
        match self {
            Value::SetU(v) => Ok(v.to_vec()),
            other => Ok(other.enumerate()?.to_vec()),
        }
    }
}

// ---------------------------------------------------------------------------------------------- KSubsetValue

/// internal code of a Java runtime exception (`IllegalArgumentException`, ...) that is not a TLC error: a Java override wraps it
pub const JAVA_RUNTIME_EXCEPTION: i32 = -1000;

/// Java: `Combinatorics.bigChoose(n, m)` as far as it fits 128 bits
fn choose_u128(n: u64, m: u64) -> Option<u128> {
    let mut c: u128 = 1;
    for i in 1..=m {
        c = c.checked_mul((n - m + i) as u128)? / i as u128;
    }
    Some(c)
}

/// log2 of `n choose m`
fn log2_choose(n: u64, m: u64) -> f64 {
    (1..=m).map(|i| ((n - m + i) as f64 / i as f64).log2()).sum()
}

/// a `BigInteger` count of k-subsets: exact while it fits 128 bits, otherwise only its logarithm
#[derive(Clone, Copy)]
enum Cnt {
    Exact(u128),
    Huge(f64),
}

impl Cnt {
    fn cmp(self, o: Cnt) -> Ordering {
        match (self, o) {
            (Cnt::Exact(a), Cnt::Exact(b)) => a.cmp(&b),
            (Cnt::Exact(_), Cnt::Huge(_)) => Ordering::Less,
            (Cnt::Huge(_), Cnt::Exact(_)) => Ordering::Greater,
            (Cnt::Huge(a), Cnt::Huge(b)) => a.partial_cmp(&b).unwrap_or(Ordering::Equal),
        }
    }
    /// compared with `2^n` (`BigInteger.ONE.shiftLeft(n)`)
    fn cmp_pow2(self, n: usize) -> Ordering {
        match self {
            Cnt::Exact(c) => {
                if n >= 128 {
                    Ordering::Less
                } else {
                    c.cmp(&(1u128 << n))
                }
            }
            Cnt::Huge(l) => l.partial_cmp(&(n as f64)).unwrap_or(Ordering::Equal),
        }
    }
}

impl Value {
    pub fn ksubset(k: i32, set: Value) -> Value {
        Value::KSubset(Rc::new((k, set)))
    }

    /// Java: `KSubsetValue.hasNoElements`
    fn ksub_no_elements(&self) -> R<bool> {
        match self {
            Value::KSubset(p) => Ok(p.0 < 0 || (p.1.is_finite() && p.1.size()? < p.0 as usize)),
            _ => Ok(false),
        }
    }

    /// Java: `KSubsetValue.count`
    fn ksub_count(&self) -> R<Cnt> {
        let Value::KSubset(p) = self else { return Ok(Cnt::Exact(0)) };
        if p.0 < 0 {
            return Ok(Cnt::Exact(0));
        }
        if p.0 == 0 {
            return Ok(Cnt::Exact(1));
        }
        let n = p.1.size()?;
        let k = p.0 as usize;
        if k > n {
            return Ok(Cnt::Exact(0));
        }
        let m = k.min(n - k) as u64;
        Ok(match choose_u128(n as u64, m) {
            Some(c) => Cnt::Exact(c),
            None => Cnt::Huge(log2_choose(n as u64, m)),
        })
    }

    /// Java: `KSubsetValue.size`
    fn ksub_size(&self) -> R<usize> {
        let Value::KSubset(p) = self else { return Ok(0) };
        match self.ksub_count()? {
            Cnt::Exact(c) if c < (1u128 << 31) => Ok(c as usize),
            _ => fail_code(JAVA_RUNTIME_EXCEPTION, format!("k={} and n={}", p.0, p.1.size()?)),
        }
    }

    /// Java: `KSubsetValue.elements` (`SubsetValue.kElements`), in normalized order
    fn ksub_enumerate(&self) -> R<Rc<Vec<Value>>> {
        let Value::KSubset(p) = self else { return Ok(Rc::new(vec![])) };
        let k = p.0;
        if self.ksub_no_elements()? {
            return Ok(Rc::new(vec![]));
        }
        if k == 0 {
            return Ok(Rc::new(vec![Value::empty_set()]));
        }
        let n = p.1.size()?;
        if n < k as usize {
            return Ok(Rc::new(vec![]));
        }
        // Java: SubsetValue.numberOfKElements
        match self.ksub_count()? {
            Cnt::Exact(c) if c < (1u128 << 63) => {
                if c > 50_000_000 {
                    return fail_code(JAVA_RUNTIME_EXCEPTION, "Subset too large.");
                }
            }
            _ => return fail_code(JAVA_RUNTIME_EXCEPTION, format!("k={} and n={}", k, n)),
        }
        let elems = p.1.enumerate()?;
        let k = k as usize;
        let mut out = Vec::new();
        let mut idx: Vec<usize> = (0..k).collect();
        loop {
            out.push(Value::Set(Rc::new(idx.iter().map(|&i| elems[i].clone()).collect())));
            let mut i = k;
            while i > 0 && idx[i - 1] == n - k + i - 1 {
                i -= 1;
            }
            if i == 0 {
                break;
            }
            idx[i - 1] += 1;
            for j in i..k {
                idx[j] = idx[j - 1] + 1;
            }
        }
        Ok(Rc::new(out))
    }

    /// Java: `KSubsetValue.compareCardinality`: `None` when a base set is infinite
    fn ksub_compare_cardinality(&self, other_base: &Value) -> R<Option<Ordering>> {
        let Value::KSubset(p) = self else { return Ok(None) };
        if !p.1.is_finite() || !other_base.is_finite() {
            return Ok(None);
        }
        let c = self.ksub_count()?;
        Ok(Some(c.cmp_pow2(other_base.size()?)))
    }

    /// Java: `KSubsetValue.equals(obj)` for a set-like `obj`
    fn ksub_eq(&self, other: &Value) -> R<bool> {
        let Value::KSubset(p) = self else { return Ok(false) };
        match other {
            Value::KSubset(q) => {
                let (n1, n2) = (self.ksub_no_elements()?, other.ksub_no_elements()?);
                if n1 || n2 {
                    return Ok(n1 && n2);
                }
                if p.0 == 0 && q.0 == 0 {
                    return Ok(true);
                }
                return Ok(p.0 == q.0 && p.1.eq_val(&q.1)?);
            }
            Value::Subset(base) => {
                if self.ksub_no_elements()? {
                    return Ok(false);
                }
                if let Some(c) = self.ksub_compare_cardinality(base)? {
                    if c != Ordering::Equal {
                        return Ok(false);
                    }
                }
                if p.0 == 0 && base.is_empty_set()? {
                    return Ok(true);
                }
            }
            _ => {}
        }
        Value::Set(self.ksub_enumerate()?).eq_val(other)
    }

    /// Java: `KSubsetValue.compareTo(obj)` for a set-like `obj`
    fn ksub_cmp(&self, other: &Value) -> R<Ordering> {
        let Value::KSubset(p) = self else { return Ok(Ordering::Equal) };
        match other {
            Value::KSubset(q) => {
                let (n1, n2) = (self.ksub_no_elements()?, other.ksub_no_elements()?);
                if n1 || n2 {
                    return Ok(if n1 && n2 {
                        Ordering::Equal
                    } else if n1 {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    });
                }
                if p.0 == q.0 {
                    if p.0 == 0 {
                        return Ok(Ordering::Equal);
                    }
                    return p.1.cmp_val(&q.1);
                }
                if p.1.is_finite() && q.1.is_finite() {
                    let c = self.ksub_count()?.cmp(other.ksub_count()?);
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                if p.1.eq_val(&q.1)? {
                    return Ok(p.0.cmp(&q.0));
                }
            }
            Value::Subset(base) => {
                if self.ksub_no_elements()? {
                    return Ok(Ordering::Less);
                }
                if let Some(c) = self.ksub_compare_cardinality(base)? {
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                if p.0 == 0 && base.is_empty_set()? {
                    return Ok(Ordering::Equal);
                }
            }
            _ => {}
        }
        Value::Set(self.ksub_enumerate()?).cmp_val(other)
    }
}

/// Java: `equals` of the infinite standard sets and of the product-like sets (`SetOfFcnsValue`, `SetOfRcdsValue`, `SetOfTuplesValue`):
/// an empty domain / field / component decides the comparison before the other constituents are looked at
fn set_eq_special(a: &Value, b: &Value) -> R<Option<bool>> {
    use Value::*;
    let builtin = |v: &Value| matches!(v, NatSet | IntSet | RealSet | StringSet | SeqOf(_));
    Ok(match (a, b) {
        (SeqOf(x), SeqOf(y)) if !(a.is_finite() || b.is_finite()) => Some(x.eq_val(y)?),
        (Subset(x), Subset(y)) if !x.is_finite() && !y.is_finite() => Some(x.eq_val(y)?),
        (x, y) if builtin(x) && builtin(y) && !x.is_finite() && !y.is_finite() => {
            Some(std::mem::discriminant(x) == std::mem::discriminant(y))
        }
        (SetOfFcns(p), SetOfFcns(q)) => {
            let (u1, u2) = (p.0.is_empty_set()?, q.0.is_empty_set()?);
            if u1 || u2 {
                return Ok(Some(u1 == u2));
            }
            let (e1, e2) = (p.1.is_empty_set()?, q.1.is_empty_set()?);
            if e1 || e2 {
                return Ok(Some(e1 == e2));
            }
            Some(p.0.eq_val(&q.0)? && p.1.eq_val(&q.1)?)
        }
        (SetOfRcds(p), SetOfRcds(q)) => {
            let e1 = a.is_empty_set()?;
            if e1 {
                return Ok(Some(b.is_empty_set()?));
            }
            if b.is_empty_set()? {
                return Ok(Some(e1));
            }
            if p.len() != q.len() {
                return Ok(Some(false));
            }
            let (mut p1, mut q1): (Vec<&(u32, Value)>, Vec<&(u32, Value)>) = (p.iter().collect(), q.iter().collect());
            p1.sort_by_key(|x| x.0);
            q1.sort_by_key(|x| x.0);
            for ((n1, s1), (n2, s2)) in p1.iter().map(|x| (&x.0, &x.1)).zip(q1.iter().map(|x| (&x.0, &x.1))) {
                if n1 != n2 || !s1.eq_val(s2)? {
                    return Ok(Some(false));
                }
            }
            Some(true)
        }
        (SetOfTuples(p), SetOfTuples(q)) => {
            let e1 = a.is_empty_set()?;
            if e1 {
                return Ok(Some(b.is_empty_set()?));
            }
            if b.is_empty_set()? {
                return Ok(Some(e1));
            }
            if p.len() != q.len() {
                return Ok(Some(false));
            }
            for (s1, s2) in p.iter().zip(q.iter()) {
                if !s1.eq_val(s2)? {
                    return Ok(Some(false));
                }
            }
            Some(true)
        }
        _ => None,
    })
}

fn is_std_infinite(v: &Value) -> bool {
    matches!(v, Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet) || (matches!(v, Value::SeqOf(_)) && !v.is_finite())
}

fn std_infinite_rank(v: &Value) -> u8 {
    match v {
        Value::NatSet => 0,
        Value::IntSet => 1,
        Value::RealSet => 2,
        Value::StringSet => 3,
        _ => 4,
    }
}

/// Java: `ModelValue` constructor: a model value whose name has more than two characters and `_` as its second one is
/// typed by its first character (`A_x` has type `A`); any other model value is untyped.
pub fn model_type(id: u32) -> Option<char> {
    thread_local! {
        /// per interned name: 0 = not computed, 1 = untyped, otherwise the type character + 2
        static TYPES: RefCell<Vec<u32>> = const { RefCell::new(Vec::new()) };
    }
    let i = id as usize;
    let cached = TYPES.with(|t| t.borrow().get(i).copied().unwrap_or(0));
    let code = if cached != 0 {
        cached
    } else {
        let name = intern::name_of(id);
        let mut cs = name.chars();
        let code = match cs.next() {
            Some(first) if name.chars().count() > 2 && cs.next() == Some('_') => first as u32 + 2,
            _ => 1,
        };
        TYPES.with(|t| {
            let mut t = t.borrow_mut();
            if t.len() <= i {
                t.resize(i + 1, 0);
            }
            t[i] = code;
        });
        code
    };
    if code == 1 {
        None
    } else {
        char::from_u32(code - 2)
    }
}

/// What TLC's fingerprint of a string value sees of it: `FP64.Extend(fp, String)` mixes only the low byte of each UTF-16
/// char (`(c ^ fp) & 0xFF`), so strings of the same length whose chars differ only in the high byte ("é" and
/// "ǩ") have equal fingerprints.  The class is computed once per interned string.
fn str_fp_class(id: u32) -> u64 {
    thread_local! {
        static CLASSES: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    }
    CLASSES.with(|c| {
        let mut c = c.borrow_mut();
        let i = id as usize;
        if i < c.len() && c[i] != 0 {
            return c[i];
        }
        let name = intern::name_of(id);
        let mut h = Hasher::new();
        let mut n = 0u64;
        for u in name.encode_utf16() {
            h.write_u64((u & 0xFF) as u64);
            n += 1;
        }
        h.write_u64(n);
        let k = h.finish() | 1;
        if c.len() <= i {
            c.resize(i + 1, 0);
        }
        c[i] = k;
        k
    })
}

/// 64-bit hasher for fingerprints (FP64 stand-in; collisions are as unlikely as with TLC's FP64)
pub struct Hasher {
    h: u64,
}

impl Hasher {
    pub fn new() -> Hasher {
        Hasher { h: 0x9E37_79B9_7F4A_7C15 }
    }
    #[inline]
    pub fn write_u64(&mut self, x: u64) {
        let mut z = (self.h ^ x).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        z ^= z >> 32;
        z = z.wrapping_mul(0xD6E8_FEB8_6659_FD93);
        self.h = z.rotate_left(27) ^ (z >> 29);
    }
    #[inline]
    pub fn finish(&self) -> u64 {
        let mut z = self.h;
        z ^= z >> 33;
        z = z.wrapping_mul(0xFF51_AFD7_ED55_8CCD);
        z ^= z >> 33;
        z = z.wrapping_mul(0xC4CE_B9FE_1A85_EC53);
        z ^ (z >> 33)
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Hasher::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_normalization_and_membership() {
        let s = Value::set_from(vec![Value::Int(3), Value::Int(1), Value::Int(3), Value::Int(2)]).unwrap();
        assert_eq!(s.to_tla(), "{1, 2, 3}");
        assert!(s.member(&Value::Int(2)).unwrap());
        assert!(!s.member(&Value::Int(5)).unwrap());
        assert!(Value::Interval(1, 3).eq_val(&s).unwrap());
    }

    #[test]
    fn functions_and_tuples() {
        let f = Value::fcn_from(vec![(Value::Int(2), Value::Int(20)), (Value::Int(1), Value::Int(10))]).unwrap();
        assert_eq!(f.to_tla(), "<<10, 20>>");
        let g = Value::fcn_from(vec![(Value::Int(3), Value::Int(1))]).unwrap();
        assert_eq!(g.to_tla(), "(3 :> 1)");
        assert_eq!(g.apply(&Value::Int(3)).unwrap().to_tla(), "1");
        assert!(g.apply(&Value::Int(4)).is_err());
        let r = Value::record(vec![(intern::intern("b"), Value::Int(2)), (intern::intern("a"), Value::Int(1))]);
        assert!(r.to_tla().starts_with("["));
    }

    #[test]
    fn incomparable_values_fail() {
        assert!(Value::Int(1).cmp_val(&Value::str("a")).is_err());
        assert!(Value::Model(0).cmp_val(&Value::Int(1)).unwrap() == Ordering::Less);
    }

    #[test]
    fn powerset_and_function_sets() {
        let s = Value::Subset(Rc::new(Value::Interval(1, 3)));
        assert_eq!(s.size().unwrap(), 8);
        let fs = Value::SetOfFcns(Rc::new((Value::Interval(1, 2), Value::Interval(0, 1))));
        assert_eq!(fs.size().unwrap(), 4);
        assert_eq!(fs.enumerate().unwrap().len(), 4);
        assert!(fs.member(&Value::tuple(vec![Value::Int(0), Value::Int(1)])).unwrap());
    }

    /// Java: SubsetValue / SetPredValue enumerators produce the elements one at a time
    #[test]
    fn try_each_visits_subsets_lazily_in_normalized_order() {
        let s = Value::Subset(Rc::new(Value::Interval(1, 3)));
        let mut seen: Vec<String> = vec![];
        assert!(s.try_each(&mut |v| { seen.push(v.to_tla()); Ok(true) }).unwrap());
        assert_eq!(seen, ["{}", "{1}", "{2}", "{3}", "{1, 2}", "{1, 3}", "{2, 3}", "{1, 2, 3}"]);
        // the same order as the materialized enumeration
        let all: Vec<String> = s.enumerate().unwrap().iter().map(|v| v.to_tla()).collect();
        assert_eq!(seen, all);
        // stopping early: the result is Ok(false) and no further element is produced
        let mut n = 0;
        assert!(!s.try_each(&mut |_| { n += 1; Ok(n < 3) }).unwrap());
        assert_eq!(n, 3);
    }

    /// Java converts `{x \in S : P}` completely before a quantifier looks at it (`EnumerableValue.elements(NORMALIZED)`)
    #[test]
    fn try_each_set_pred_is_evaluated_completely_first() {
        use std::cell::Cell;
        let calls = Rc::new(Cell::new(0));
        let c2 = calls.clone();
        let p = Value::SetPred(Rc::new(SetPred {
            base: Value::Interval(1, 10),
            pred: Box::new(move |v: &Value| {
                c2.set(c2.get() + 1);
                Ok(v.as_int()? % 2 == 0)
            }),
            cache: RefCell::new(None),
        }));
        // stopping at the first element still evaluated the predicate for all 10 elements
        let mut first = None;
        assert!(!p.try_each(&mut |v| { first = Some(v.to_tla()); Ok(false) }).unwrap());
        assert_eq!(first.as_deref(), Some("2"));
        assert_eq!(calls.get(), 10);
        // the result is cached: walking it again does not call the predicate
        let mut all = vec![];
        assert!(p.try_each(&mut |v| { all.push(v.to_tla()); Ok(true) }).unwrap());
        assert_eq!(all, ["2", "4", "6", "8", "10"]);
        assert_eq!(calls.get(), 10);
    }

    /// an error in the predicate for an element after the witness is raised, as in Java
    #[test]
    fn try_each_set_pred_error_behind_the_witness_is_raised() {
        let p = Value::SetPred(Rc::new(SetPred {
            base: Value::Subset(Rc::new(Value::Interval(1, 3))),
            pred: Box::new(|v: &Value| match v {
                Value::Set(e) if e.len() == 3 => fail("boom"),
                _ => Ok(true),
            }),
            cache: RefCell::new(None),
        }));
        assert!(p.try_each(&mut |_| Ok(false)).is_err());
    }

    /// Java: KSubsetValue (`FiniteSetsExt!kSubset`)
    #[test]
    fn ksubset_follows_java() {
        let k24 = Value::ksubset(2, Value::Interval(1, 4));
        let all: Vec<String> = k24.enumerate().unwrap().iter().map(|v| v.to_tla()).collect();
        assert_eq!(all, ["{1, 2}", "{1, 3}", "{1, 4}", "{2, 3}", "{2, 4}", "{3, 4}"]);
        assert_eq!(k24.size().unwrap(), 6);
        // a negative or too large k has no element, k = 0 is {{}} whatever the base set is
        assert!(Value::ksubset(-1, Value::NatSet).is_empty_set().unwrap());
        assert!(Value::ksubset(4, Value::Interval(1, 3)).is_empty_set().unwrap());
        let k0 = Value::ksubset(0, Value::NatSet);
        assert!(k0.is_finite());
        assert_eq!(k0.size().unwrap(), 1);
        assert!(!Value::ksubset(1, Value::NatSet).is_finite());
        assert!(k0.eq_val(&Value::set_from(vec![Value::empty_set()]).unwrap()).unwrap());
        assert!(Value::ksubset(0, Value::Interval(1, 3)).eq_val(&Value::ksubset(0, Value::Interval(1, 4))).unwrap());
        assert!(!Value::ksubset(1, Value::Interval(1, 3)).eq_val(&Value::ksubset(2, Value::Interval(1, 3))).unwrap());
        // membership: size first, then every element in the base set
        assert!(k24.member(&Value::set_from(vec![Value::Int(1), Value::Int(4)]).unwrap()).unwrap());
        assert!(!k24.member(&Value::set_from(vec![Value::Int(1)]).unwrap()).unwrap());
        // comparison with the power set needs no enumeration of it
        let big = Value::ksubset(2, Value::Interval(1, 64));
        assert_eq!(big.size().unwrap(), 2016);
        assert!(!big.eq_val(&Value::Subset(Rc::new(Value::Interval(1, 64)))).unwrap());
        let e = Value::ksubset(32, Value::Interval(1, 64)).size().unwrap_err();
        assert_eq!((e.code, e.msg.as_str()), (JAVA_RUNTIME_EXCEPTION, "k=32 and n=64"));
        assert_eq!(k24.to_tla(), "{{1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}}");
        assert!(Value::ksubset(2, Value::Interval(1, 12)).to_tla().ends_with("in SUBSET (1..12) : Cardinality(s) = 2}"));
    }
}

#[cfg(test)]
mod size_tests {
    #[test]
    fn print_sizes() {
        eprintln!("size Value = {}", std::mem::size_of::<super::Value>());
        eprintln!("size Slot = {}", std::mem::size_of::<crate::ir::Slot>());
        eprintln!("size Node = {}", std::mem::size_of::<crate::ir::Node>());
    }
}
