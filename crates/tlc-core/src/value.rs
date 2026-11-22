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
}

pub type R<T> = Result<T, Box<TlcErr>>;

pub fn fail_code<T>(code: i32, msg: impl Into<String>) -> R<T> {
    Err(Box::new(TlcErr { code, msg: msg.into(), not_ported: false, trail: vec![] }))
}

/// `Assert.fail(msg)` -> EC.GENERAL
pub fn fail<T>(msg: impl Into<String>) -> R<T> {
    fail_code(crate::ec::GENERAL, msg)
}

pub fn not_ported<T>(what: impl Into<String>) -> R<T> {
    Err(Box::new(TlcErr { code: crate::mp::NOT_PORTED, msg: what.into(), not_ported: true, trail: vec![] }))
}

// ---------------------------------------------------------------------------------------------- values

pub struct Fcn {
    /// sorted domain (never a `1..n` integer domain: those are tuples)
    pub dom: Rc<Vec<Value>>,
    pub vals: Vec<Value>,
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
            Value::Fcn(Rc::new(Fcn { dom: Rc::new(dom), vals }))
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
                let base = p.base.enumerate()?;
                let mut out = Vec::new();
                for e in base.iter() {
                    if (p.pred)(e)? {
                        out.push(e.clone());
                    }
                }
                let r = Rc::new(out);
                *p.cache.borrow_mut() = Some(r.clone());
                Ok(r)
            }
            Value::Subset(s) => {
                let base = s.enumerate()?;
                let n = base.len();
                if n >= 31 {
                    return fail(format!("Attempted to enumerate SUBSET of a set with {} elements.", n));
                }
                let mut out = Vec::with_capacity(1usize << n);
                for mask in 0u64..(1u64 << n) {
                    let mut sub = Vec::new();
                    for (i, e) in base.iter().enumerate() {
                        if mask & (1 << i) != 0 {
                            sub.push(e.clone());
                        }
                    }
                    out.push(Value::Set(Rc::new(sub)));
                }
                Ok(Value::set_from(out)?.enumerate()?)
            }
            Value::SetOfFcns(p) => {
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
                let a = p.0.enumerate()?;
                let mut out = vec![];
                for e in a.iter() {
                    if p.1.member(e)? {
                        out.push(e.clone());
                    }
                }
                Ok(Rc::new(out))
            }
            Value::SetDiff(p) => {
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
            Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet | Value::SeqOf(_) => false,
            Value::SetPred(p) => p.base.is_finite(),
            Value::SetCup(p) => p.0.is_finite() && p.1.is_finite(),
            Value::SetCap(p) => p.0.is_finite() || p.1.is_finite(),
            Value::SetDiff(p) => p.0.is_finite(),
            Value::Subset(s) => s.is_finite(),
            Value::SetOfFcns(p) => p.0.is_finite() && p.1.is_finite(),
            Value::SetOfRcds(fs) => fs.iter().all(|(_, s)| s.is_finite()),
            Value::SetOfTuples(ss) => ss.iter().all(|s| s.is_finite()),
            Value::BigUnion(s) => s.is_finite(),
            _ => true,
        }
    }

    /// cardinality of a finite set
    pub fn size(&self) -> R<usize> {
        match self {
            Value::Set(v) => Ok(v.len()),
            Value::Interval(lo, hi) => Ok(if hi < lo { 0 } else { (*hi as i64 - *lo as i64 + 1) as usize }),
            Value::Subset(s) => {
                let n = s.size()?;
                if n >= 63 {
                    return fail("Overflow when computing the size of a SUBSET.");
                }
                Ok(1usize << n)
            }
            Value::SetOfFcns(p) => {
                let (nd, nr) = (p.0.size()?, p.1.size()?);
                let mut sz: usize = 1;
                for _ in 0..nd {
                    sz = match sz.checked_mul(nr) {
                        Some(x) => x,
                        None => return fail("Overflow when computing the size of a set of functions."),
                    };
                }
                Ok(sz)
            }
            Value::SetOfRcds(fs) => {
                let mut sz: usize = 1;
                for (_, s) in fs.iter() {
                    sz = sz.saturating_mul(s.size()?);
                }
                Ok(sz)
            }
            Value::SetOfTuples(ss) => {
                let mut sz: usize = 1;
                for s in ss.iter() {
                    sz = sz.saturating_mul(s.size()?);
                }
                Ok(sz)
            }
            Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet | Value::SeqOf(_) => {
                fail(format!("Attempted to compute the number of elements in the non-enumerable set\n{}", self.to_tla()))
            }
            v if v.is_set_like() => Ok(v.enumerate()?.len()),
            v => fail(format!("Attempted to compute the number of elements in the non-set value\n{}", v.to_tla())),
        }
    }

    // ------------------------------------------------------------------ membership

    pub fn member(&self, e: &Value) -> R<bool> {
        match self {
            Value::Set(v) => {
                // binary search with the total order; errors on incomparable elements
                if v.is_empty() {
                    return Ok(false);
                }
                let (mut lo, mut hi) = (0usize, v.len());
                while lo < hi {
                    let mid = (lo + hi) / 2;
                    match v[mid].cmp_val(e)? {
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
                _ => fail(format!("Attempted to check if the non-integer value:\n{}\nis in Nat.", e.to_tla())),
            },
            Value::IntSet => match e {
                Value::Int(_) => Ok(true),
                Value::Model(_) => Ok(false),
                _ => fail(format!("Attempted to check if the non-integer value:\n{}\nis in Int.", e.to_tla())),
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
                    return fail(format!("Attempted to check if the non-set value\n{}\nis in SUBSET", e.to_tla()));
                }
                e.subseteq(s)
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
                for v in f.fcn_values()?.iter() {
                    if !p.1.member(v)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Value::SetOfRcds(fs) => {
                let f = e.force_fcn()?;
                let (dom, vals) = match f.fcn_parts() {
                    Some(x) => x,
                    None => return Ok(false),
                };
                if dom.len() != fs.len() {
                    return Ok(false);
                }
                for (i, d) in dom.iter().enumerate() {
                    match d {
                        Value::Str(id) => match fs.iter().find(|(n, _)| n == id) {
                            Some((_, s)) => {
                                if !s.member(&vals[i])? {
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
                _ => Ok(false),
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
                    "Attempted to apply tuple:\n{}\nto argument {} which is out of domain.",
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
                    return fail(format!(
                        "Attempted to apply function:\n{}\nto argument {}, which is not in the domain of the function.",
                        self.to_tla(),
                        arg.to_tla()
                    ));
                }
                (l.apply)(arg)
            }
            v => fail(format!("Attempted to apply the non-function\n{}\nto argument {}", v.to_tla(), arg.to_tla())),
        }
    }

    fn search(dom: &[Value], x: &Value) -> R<Option<usize>> {
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
                    Ok(Value::Fcn(Rc::new(Fcn { dom: f.dom.clone(), vals })))
                }
                None => Ok(self.clone()),
            },
            Value::FcnLam(_) => self.force_fcn()?.except1(arg, v),
            _ => fail(format!("Attempted to apply EXCEPT to the non-function\n{}", self.to_tla())),
        }
    }

    // ------------------------------------------------------------------ comparison

    fn set_like_cmp_ready(&self) -> bool {
        self.is_set_like()
    }

    /// `Value.compareTo`
    pub fn cmp_val(&self, o: &Value) -> R<Ordering> {
        use Value::*;
        match (self, o) {
            (Int(a), Int(b)) => Ok(a.cmp(b)),
            (Str(a), Str(b)) => Ok(a.cmp(b)),
            (Bool(a), Bool(b)) => Ok(a.cmp(b)),
            (Model(a), Model(b)) => Ok(a.cmp(b)),
            (Model(_), _) => Ok(Ordering::Less),
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
            (Int(a), Int(b)) => Ok(a == b),
            (Str(a), Str(b)) => Ok(a == b),
            (Bool(a), Bool(b)) => Ok(a == b),
            (Model(a), Model(b)) => Ok(a == b),
            (Model(_), _) | (_, Model(_)) => Ok(false),
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
                if !a.is_finite() || !b.is_finite() {
                    return fail(format!(
                        "Attempted to check equality of the infinite set\n{}\nwith the value:\n{}",
                        a.to_tla(),
                        b.to_tla()
                    ));
                }
                Ok(a.cmp_val(b)? == Ordering::Equal)
            }
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
            Value::Subset(s) => {
                out.push_str("SUBSET ");
                s.write_tla(out);
            }
            v => match v.enumerate() {
                Ok(e) => Value::Set(e).write_tla(out),
                Err(_) => out.push_str("<set>"),
            },
        }
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
                h.write_u64(*id as u64);
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
                h.write_u64(0x70);
                h.write_u64(f.dom.len() as u64);
                for (d, v) in f.dom.iter().zip(f.vals.iter()) {
                    d.hash_into(h)?;
                    v.hash_into(h)?;
                }
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
                    Ok(Value::Fcn(Rc::new(Fcn { dom: f.dom.clone(), vals })))
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

    fn needs_normalize(&self) -> bool {
        match self {
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => false,
            Value::Set(v) => v.iter().any(|e| e.needs_normalize()),
            Value::Tuple(t) => t.iter().any(|e| e.needs_normalize()),
            Value::Fcn(f) => f.vals.iter().any(|e| e.needs_normalize()) || f.dom.iter().any(|e| e.needs_normalize()),
            _ => true,
        }
    }
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
