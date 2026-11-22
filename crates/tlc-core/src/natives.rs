//! Port of `tlc2.module.*` (Naturals, Integers, Sequences, FiniteSets, TLC, Bags, ...): native implementations that
//! TLC substitutes for the dummy definitions of the standard modules (keyed by module and operator name).

use crate::ec;
use crate::eval::Ev;
use crate::ir::*;
use crate::value::*;
use std::rc::Rc;
use tla_sany::intern;

fn arg(ev: &Ev, a: &mut Vec<Slot>, i: usize, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = std::mem::replace(&mut a[i], Slot::Unset);
    ev.force_slot(s, s0, s1)
}

fn int_arg(ev: &Ev, a: &mut Vec<Slot>, i: usize, which: &str, op: &str, s0: &[Value], s1: &[Value]) -> R<i32> {
    match arg(ev, a, i, s0, s1)? {
        Value::Int(n) => Ok(n),
        v => fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR_AN,
            format!("The {} argument of {} should be an integer, but instead it is:\n{}", which, op, v.to_tla()),
        ),
    }
}

fn overflow<T>(expr: String) -> R<T> {
    fail_code(ec::TLC_MODULE_OVERFLOW, format!("Overflow when computing {}", expr))
}

type N = fn(&Ev, &mut Vec<Slot>, &[Value], &[Value]) -> R<Value>;

fn plus(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "+", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", "+", s0, s1)?;
    match x.checked_add(y) {
        Some(r) => Ok(Value::Int(r)),
        None => overflow(format!("{}+{}", x, y)),
    }
}

fn minus(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "-", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", "-", s0, s1)?;
    match x.checked_sub(y) {
        Some(r) => Ok(Value::Int(r)),
        None => overflow(format!("{}-{}", x, y)),
    }
}

fn times(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "*", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", "*", s0, s1)?;
    match x.checked_mul(y) {
        Some(r) => Ok(Value::Int(r)),
        None => overflow(format!("{}*{}", x, y)),
    }
}

fn uminus(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "-", s0, s1)?;
    match x.checked_neg() {
        Some(r) => Ok(Value::Int(r)),
        None => overflow(format!("-{}", x)),
    }
}

fn lt(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "<", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", "<", s0, s1)?;
    Ok(Value::Bool(x < y))
}
fn le(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "<=", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", "<=", s0, s1)?;
    Ok(Value::Bool(x <= y))
}
fn gt(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", ">", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", ">", s0, s1)?;
    Ok(Value::Bool(x > y))
}
fn ge(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", ">=", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", ">=", s0, s1)?;
    Ok(Value::Bool(x >= y))
}

fn dotdot(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "..", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", "..", s0, s1)?;
    Ok(Value::Interval(x, y))
}

fn intdiv(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let n1 = int_arg(ev, a, 0, "first", "\\div", s0, s1)?;
    let n2 = int_arg(ev, a, 1, "second", "\\div", s0, s1)?;
    if n2 == 0 {
        return fail_code(ec::TLC_MODULE_DIVISION_BY_ZERO, "The second argument of \\div is 0.");
    }
    let mut q = n1.wrapping_div(n2);
    if q < 0 && q.wrapping_mul(n2) != n1 {
        q -= 1;
    }
    Ok(Value::Int(q))
}

fn modulo(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let n1 = int_arg(ev, a, 0, "first", "%", s0, s1)?;
    let n2 = int_arg(ev, a, 1, "second", "%", s0, s1)?;
    if n2 <= 0 {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR,
            format!("The second argument of % should be a positive number, but instead it is:\n{}", n2),
        );
    }
    let mut r = n1 % n2;
    if r < 0 {
        r += n2;
    }
    Ok(Value::Int(r))
}

fn expt(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let m = int_arg(ev, a, 0, "first", "^", s0, s1)?;
    let n = int_arg(ev, a, 1, "second", "^", s0, s1)?;
    if n < 0 {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR,
            format!("The second argument of ^ should be a nonnegative number, but instead it is:\n{}", n),
        );
    }
    if m == 0 && n == 0 {
        return fail_code(ec::TLC_MODULE_NULL_POWER_NULL, "0^0 is undefined.");
    }
    let mut r: i64 = 1;
    let mut base = m as i64;
    let mut e = n;
    while e > 0 {
        if e & 1 == 1 {
            r = r.saturating_mul(base);
            if r > i32::MAX as i64 || r < i32::MIN as i64 {
                return overflow(format!("{}^{}", m, n));
            }
        }
        e >>= 1;
        if e > 0 {
            base = base.saturating_mul(base);
            if base > i32::MAX as i64 * 2 || base < i32::MIN as i64 * 2 {
                // may still be fine if remaining exponent bits are 0, but then e would be 0; any further use overflows
                let mut rest = e;
                let mut need = false;
                while rest > 0 {
                    if rest & 1 == 1 {
                        need = true;
                    }
                    rest >>= 1;
                }
                if need {
                    return overflow(format!("{}^{}", m, n));
                }
            }
        }
    }
    Ok(Value::Int(r as i32))
}

fn nat(_: &Ev, _: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    Ok(Value::NatSet)
}
fn int(_: &Ev, _: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    Ok(Value::IntSet)
}
fn real(_: &Ev, _: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    Ok(Value::RealSet)
}

// ---------------------------------------------------------------------------------------------- Sequences

fn as_seq(v: &Value, who: &str) -> R<Vec<Value>> {
    match v {
        Value::Tuple(t) => Ok(t.to_vec()),
        Value::FcnLam(_) => match v.force_fcn()? {
            Value::Tuple(t) => Ok(t.to_vec()),
            other => fail_code(
                ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE,
                format!("Applying {} to the following value,\nwhich is not a sequence:\n{}", who, other.to_tla()),
            ),
        },
        _ => fail_code(
            ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE,
            format!("Applying {} to the following value,\nwhich is not a sequence:\n{}", who, v.to_tla()),
        ),
    }
}

fn seq_set(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0, s0, s1)?;
    Ok(Value::SeqOf(Rc::new(s)))
}

fn len(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let v = arg(ev, a, 0, s0, s1)?;
    Ok(Value::Int(as_seq(&v, "Len")?.len() as i32))
}

fn concat(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let y = arg(ev, a, 1, s0, s1)?;
    let mut s = as_seq(&x, "\\o")?;
    s.extend(as_seq(&y, "\\o")?);
    Ok(Value::tuple(s))
}

fn append(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let e = arg(ev, a, 1, s0, s1)?;
    let mut s = as_seq(&x, "Append")?;
    s.push(e);
    Ok(Value::tuple(s))
}

fn head(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let s = as_seq(&x, "Head")?;
    match s.first() {
        Some(v) => Ok(v.clone()),
        None => fail_code(ec::TLC_MODULE_APPLY_EMPTY_SEQ, "Attempted to apply Head to the empty sequence."),
    }
}

fn tail(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let s = as_seq(&x, "Tail")?;
    if s.is_empty() {
        return fail_code(ec::TLC_MODULE_APPLY_EMPTY_SEQ, "Attempted to apply Tail to the empty sequence.");
    }
    Ok(Value::tuple(s[1..].to_vec()))
}

fn subseq(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let m = int_arg(ev, a, 1, "second", "SubSeq", s0, s1)?;
    let n = int_arg(ev, a, 2, "third", "SubSeq", s0, s1)?;
    let s = as_seq(&x, "SubSeq")?;
    if n < m {
        return Ok(Value::tuple(vec![]));
    }
    if m < 1 || (m as usize) > s.len() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN,
            format!(
                "The second argument of SubSeq must be in the domain of its first argument:\n{}\n, but instead it is\n{}",
                Value::tuple(s.clone()).to_tla(),
                m
            ),
        );
    }
    if (n as usize) > s.len() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN,
            format!(
                "The third argument of SubSeq must be in the domain of its first argument:\n{}\n, but instead it is\n{}",
                Value::tuple(s.clone()).to_tla(),
                n
            ),
        );
    }
    Ok(Value::tuple(s[(m - 1) as usize..n as usize].to_vec()))
}

fn select_seq(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let test = match std::mem::replace(&mut a[1], Slot::Unset) {
        Slot::Op(c) => c,
        _ => return fail("The second argument of SelectSeq must be an operator."),
    };
    let s = as_seq(&x, "SelectSeq")?;
    let mut out = vec![];
    for e in s {
        let r = ev.apply_closure_slots(&test, vec![Slot::V(e.clone())], s0, s1)?;
        if r.as_bool()? {
            out.push(e);
        }
    }
    Ok(Value::tuple(out))
}

// ---------------------------------------------------------------------------------------------- FiniteSets

fn is_finite_set(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0, s0, s1)?;
    if !s.is_set_like() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR_AN,
            format!("The first argument of IsFiniteSet should be a set, but instead it is:\n{}", s.to_tla()),
        );
    }
    Ok(Value::Bool(s.is_finite()))
}

fn cardinality(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0, s0, s1)?;
    if !s.is_set_like() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR_AN,
            format!("The first argument of Cardinality should be a set, but instead it is:\n{}", s.to_tla()),
        );
    }
    if !s.is_finite() {
        return fail_code(ec::TLC_MODULE_COMPUTING_CARDINALITY, format!("Attempted to compute cardinality of the value\n{}", s.to_tla()));
    }
    let n = s.size()?;
    if n > i32::MAX as usize {
        return overflow("Cardinality".into());
    }
    Ok(Value::Int(n as i32))
}

// ---------------------------------------------------------------------------------------------- TLC

fn print(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let v1 = arg(ev, a, 0, s0, s1)?.normalize()?;
    let v2 = arg(ev, a, 1, s0, s1)?;
    let n2 = v2.normalize()?;
    ev.out.borrow_mut().push(format!("{}  {}", crate::pprint::ppr(&v1.to_tla()), crate::pprint::ppr(&n2.to_tla())));
    Ok(v2)
}

fn print_t(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let v = arg(ev, a, 0, s0, s1)?.normalize()?;
    ev.out.borrow_mut().push(crate::pprint::ppr(&v.to_tla()));
    Ok(Value::Bool(true))
}

fn assert_(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let v1 = arg(ev, a, 0, s0, s1)?;
    if let Value::Bool(true) = v1 {
        return Ok(v1);
    }
    let v2 = std::mem::replace(&mut a[1], Slot::Unset);
    let msg = match ev.force_slot(v2, s0, s1) {
        Ok(v) => match &v {
            Value::Str(id) => intern::name_of(*id).to_string(),
            other => other.to_tla(),
        },
        Err(e) => return Err(e),
    };
    fail_code(ec::TLC_VALUE_ASSERT_FAILED, format!("The first argument of Assert evaluated to FALSE; the second argument was:\n{}", msg))
}

fn to_string(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let v = arg(ev, a, 0, s0, s1)?.normalize()?;
    Ok(Value::str(&v.to_tla()))
}

fn java_time(_: &Ev, _: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
    Ok(Value::Int((t as i32) & 0x7FFF_FFFF))
}

fn make_fcn(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let d = arg(ev, a, 0, s0, s1)?;
    let e = arg(ev, a, 1, s0, s1)?;
    Value::fcn_from(vec![(d, e)])
}

fn combine_fcn(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let f = arg(ev, a, 0, s0, s1)?.force_fcn()?;
    let g = arg(ev, a, 1, s0, s1)?.force_fcn()?;
    let (df, vf) = match f.fcn_parts() {
        Some(p) => p,
        None => return fail(format!("The first argument of @@ must be a function, but instead it is:\n{}", f.to_tla())),
    };
    let (dg, vg) = match g.fcn_parts() {
        Some(p) => p,
        None => return fail(format!("The second argument of @@ must be a function, but instead it is:\n{}", g.to_tla())),
    };
    let mut pairs: Vec<(Value, Value)> = df.into_iter().zip(vf.into_iter()).collect();
    for (d, v) in dg.into_iter().zip(vg.into_iter()) {
        let mut found = false;
        for (d0, _) in pairs.iter() {
            if d0.cmp_val(&d)? == std::cmp::Ordering::Equal {
                found = true;
                break;
            }
        }
        if !found {
            pairs.push((d, v));
        }
    }
    Value::fcn_from(pairs)
}

fn permutations(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0, s0, s1)?;
    let elems = s.enumerate()?;
    let n = elems.len();
    let mut idx: Vec<usize> = (0..n).collect();
    let mut out: Vec<Value> = vec![];
    // all permutations as functions elems[i] -> elems[perm[i]]
    fn rec(k: usize, idx: &mut Vec<usize>, elems: &[Value], out: &mut Vec<Value>) -> R<()> {
        if k == idx.len() {
            let pairs: Vec<(Value, Value)> = (0..idx.len()).map(|i| (elems[i].clone(), elems[idx[i]].clone())).collect();
            out.push(Value::fcn_from(pairs)?);
            return Ok(());
        }
        for i in k..idx.len() {
            idx.swap(k, i);
            rec(k + 1, idx, elems, out)?;
            idx.swap(k, i);
        }
        Ok(())
    }
    rec(0, &mut idx, &elems, &mut out)?;
    Value::set_from(out)
}

/// the next pseudo-random double of the shared generator (Java: `RandomEnumerableValues.get().nextDouble()`)
fn next_double(ev: &Ev) -> f64 {
    let mut g = ev.rng.borrow_mut();
    g.get_or_insert_with(|| crate::jrandom::JRandom::new(ev.seed.get())).next_double()
}

// Java: TLC.RandomElement
fn random_element_of(ev: &Ev, v: &Value) -> R<Value> {
    let wrong = || {
        fail_code(
            ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE,
            format!(
                "Applying RandomElement to a finite set, but instead it is:
{}",
                crate::pprint::ppr(&v.to_tla())
            ),
        )
    };
    match v {
        Value::SetOfFcns(p) => {
            let (dom, range) = &**p;
            if !dom.is_set_like() {
                return wrong();
            }
            let dom = dom.enumerate()?;
            let mut pairs = Vec::with_capacity(dom.len());
            for d in dom.iter() {
                pairs.push((d.clone(), random_element_of(ev, range)?));
            }
            Value::fcn_from(pairs)
        }
        Value::SetOfRcds(fields) => {
            let mut pairs = Vec::with_capacity(fields.len());
            for (name, set) in fields.iter() {
                pairs.push((Value::Str(*name), random_element_of(ev, set)?));
            }
            Value::fcn_from(pairs)
        }
        Value::SetOfTuples(sets) => {
            let mut out = Vec::with_capacity(sets.len());
            for s in sets.iter() {
                out.push(random_element_of(ev, s)?);
            }
            Ok(Value::tuple(out))
        }
        Value::Interval(lo, hi) => {
            if hi < lo {
                return fail_code(ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE, "Attempted to select a random element of an empty set.".to_string());
            }
            let sz = (*hi as i64 - *lo as i64 + 1) as f64;
            let index = (next_double(ev) * sz).floor() as i64;
            Ok(Value::Int((*lo as i64 + index) as i32))
        }
        _ => {
            if !v.is_set_like() || matches!(v, Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet | Value::SeqOf(_)) {
                return wrong();
            }
            let elems = v.enumerate()?;
            if elems.is_empty() {
                return fail_code(ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE, "Attempted to select a random element of an empty set.".to_string());
            }
            let index = (next_double(ev) * elems.len() as f64).floor() as usize;
            Ok(elems[index].clone())
        }
    }
}

fn random_element(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0, s0, s1)?;
    random_element_of(ev, &s)
}

fn sort_seq(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let cmp = match std::mem::replace(&mut a[1], Slot::Unset) {
        Slot::Op(c) => c,
        _ => return fail("The second argument of SortSeq must be an operator."),
    };
    let s = as_seq(&x, "SortSeq")?;
    let mut err: Option<Box<TlcErr>> = None;
    let mut v = s;
    v.sort_by(|p, q| {
        if err.is_some() {
            return std::cmp::Ordering::Equal;
        }
        match ev.apply_closure_slots(&cmp, vec![Slot::V(p.clone()), Slot::V(q.clone())], s0, s1).and_then(|r| r.as_bool()) {
            Ok(true) => std::cmp::Ordering::Less,
            Ok(false) => {
                match ev.apply_closure_slots(&cmp, vec![Slot::V(q.clone()), Slot::V(p.clone())], s0, s1).and_then(|r| r.as_bool()) {
                    Ok(true) => std::cmp::Ordering::Greater,
                    Ok(false) => std::cmp::Ordering::Equal,
                    Err(e) => {
                        err = Some(e);
                        std::cmp::Ordering::Equal
                    }
                }
            }
            Err(e) => {
                err = Some(e);
                std::cmp::Ordering::Equal
            }
        }
    });
    if let Some(e) = err {
        return Err(e);
    }
    Ok(Value::tuple(v))
}

fn tlc_get(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let k = arg(ev, a, 0, s0, s1)?;
    match &k {
        Value::Int(i) => Ok(ev.tlc_registers.borrow().get(i).cloned().unwrap_or(Value::Int(0))),
        Value::Str(id) => {
            let name = intern::name_of(*id);
            let idx = match &*name {
                "level" => Some(0),
                "generated" => Some(1),
                "distinct" => Some(2),
                "queue" => Some(3),
                "diameter" => Some(4),
                "duration" => Some(5),
                _ => None,
            };
            if let Some(i) = idx {
                let v = ev.counters.get()[i];
                return match i32::try_from(v) {
                    Ok(n) => Ok(Value::Int(n)),
                    Err(_) => fail_code(ec::TLC_MODULE_OVERFLOW, format!("Overflow when computing {}", v)),
                };
            }
            match ev.stats.borrow().get(&*name) {
                Some(v) => Ok(v.clone()),
                None => fail_code(ec::TLC_MODULE_TLCGET_UNDEFINED, format!("TLCGet({}) is undefined.", k.to_tla())),
            }
        }
        _ => fail(format!("TLCGet was applied to the unsupported argument {}", k.to_tla())),
    }
}

fn tlc_set(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let k = arg(ev, a, 0, s0, s1)?;
    let v = arg(ev, a, 1, s0, s1)?;
    if let Value::Int(i) = k {
        ev.tlc_registers.borrow_mut().insert(i, v);
        Ok(Value::Bool(true))
    } else {
        fail(format!("TLCSet was applied to the unsupported argument {}", k.to_tla()))
    }
}

// ------------------------------------------------------------------ community modules (tlc2.overrides.*)

fn op_arg(a: &mut Vec<Slot>, i: usize, who: &str) -> R<Rc<OpClosure>> {
    match std::mem::replace(&mut a[i], Slot::Unset) {
        Slot::Op(c) => Ok(c),
        _ => fail(format!("The argument of {} must be an operator.", who)),
    }
}

fn module_arg_err<T>(which: &str, op: &str, what: &str, v: &Value) -> R<T> {
    fail_code(
        ec::TLC_MODULE_ARGUMENT_ERROR,
        format!("The {} argument of {} should be a {}, but instead it is:\n{}", which, op, what, crate::pprint::ppr(&v.to_tla())),
    )
}


/// `+` / `*` applied to two integers without going through the generic call machinery
fn fast_bin(op: &Rc<OpClosure>, x: &Value, y: &Value) -> Option<Value> {
    if let (OpClosure::Def(d), Value::Int(p), Value::Int(q)) = (&**op, x, y) {
        if d.native.get().is_some() && matches!(&*d.module, "Naturals" | "Integers") {
            return match &*d.name {
                "+" => p.checked_add(*q).map(Value::Int),
                "*" => p.checked_mul(*q).map(Value::Int),
                _ => None,
            };
        }
    }
    None
}

/// Java: Functions.foldFunctionOnSet: fold in the order of the (normalized) set: acc := op(fun[x], acc)
fn fold_function_on_set(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let op = op_arg(a, 0, "FoldFunctionOnSet")?;
    let base = arg(ev, a, 1, s0, s1)?;
    let fun = arg(ev, a, 2, s0, s1)?;
    let set = arg(ev, a, 3, s0, s1)?;
    if !fun.is_fcn_like() {
        return module_arg_err("third", "FoldFunctionOnSet", "function", &fun);
    }
    if !set.is_set_like() {
        return module_arg_err("fourth", "FoldFunctionOnSet", "set", &set);
    }
    let elems = set.enumerate()?;
    let mut acc = base;
    for x in elems.iter() {
        let fx = fun.apply(x)?;
        if let Some(v) = fast_bin(&op, &fx, &acc) {
            acc = v;
            continue;
        }
        acc = ev.apply_closure_slots(&op, vec![Slot::V(fx), Slot::V(acc)], s0, s1)?;
    }
    Ok(acc)
}

fn fold_function(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let op = op_arg(a, 0, "FoldFunction")?;
    let base = arg(ev, a, 1, s0, s1)?;
    let fun = arg(ev, a, 2, s0, s1)?;
    if !fun.is_fcn_like() {
        return module_arg_err("third", "FoldFunction", "function", &fun);
    }
    let dom = fun.domain()?;
    let elems = dom.enumerate()?;
    let mut acc = base;
    for x in elems.iter() {
        let fx = fun.apply(x)?;
        if let Some(v) = fast_bin(&op, &fx, &acc) {
            acc = v;
            continue;
        }
        acc = ev.apply_closure_slots(&op, vec![Slot::V(fx), Slot::V(acc)], s0, s1)?;
    }
    Ok(acc)
}

/// Java: FiniteSetsExt.foldSet
fn fold_set(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let op = op_arg(a, 0, "FoldSet")?;
    let base = arg(ev, a, 1, s0, s1)?;
    let set = arg(ev, a, 2, s0, s1)?;
    if !set.is_set_like() {
        return module_arg_err("third", "FoldSet", "set", &set);
    }
    let elems = set.enumerate()?;
    let mut acc = base;
    for x in elems.iter() {
        acc = ev.apply_closure_slots(&op, vec![Slot::V(x.clone()), Slot::V(acc)], s0, s1)?;
    }
    Ok(acc)
}

/// Java: FiniteSetsExt.quantify
fn quantify(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let set = arg(ev, a, 0, s0, s1)?;
    let test = op_arg(a, 1, "Quantify")?;
    if !set.is_set_like() {
        return module_arg_err("first", "Quantify", "set", &set);
    }
    let elems = set.enumerate()?;
    let mut n = 0;
    for x in elems.iter() {
        match ev.apply_closure_slots(&test, vec![Slot::V(x.clone())], s0, s1)? {
            Value::Bool(true) => n += 1,
            Value::Bool(false) => {}
            _ => return fail_code(ec::TLC_MODULE_ARGUMENT_ERROR, "The second argument of Quantify should be a boolean-valued operator, but instead it is:\nan operator".to_string()),
        }
    }
    Ok(Value::Int(n))
}

/// Java: Functions.IsInjective
fn is_injective(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let f = arg(ev, a, 0, s0, s1)?;
    let vals = match f.force_fcn()?.fcn_parts() {
        Some((_, v)) => v,
        None => {
            return fail_code(
                ec::TLC_MODULE_ONE_ARGUMENT_ERROR,
                format!("The argument of IsInjective should be a function, but instead it is:\n{}", crate::pprint::ppr(&f.to_tla())),
            )
        }
    };
    for i in 0..vals.len() {
        for j in i + 1..vals.len() {
            if vals[i].eq_val(&vals[j])? {
                return Ok(Value::Bool(false));
            }
        }
    }
    Ok(Value::Bool(true))
}

/// Java: Functions.antiFunction
fn anti_function(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let f = arg(ev, a, 0, s0, s1)?;
    let (dom, vals) = match f.force_fcn()?.fcn_parts() {
        Some(p) => p,
        None => {
            return fail_code(
                ec::TLC_MODULE_ONE_ARGUMENT_ERROR,
                format!("The argument of AntiFunction should be a functions, but instead it is:\n{}", crate::pprint::ppr(&f.to_tla())),
            )
        }
    };
    let mut seen: Vec<(Value, Value)> = vec![];
    for (d, v) in dom.iter().zip(vals.iter()) {
        let mut dup = false;
        for (k, _) in &seen {
            if k.eq_val(v)? {
                dup = true;
                break;
            }
        }
        if !dup {
            seen.push((v.clone(), d.clone()));
        }
    }
    Value::fcn_from(seen)
}

/// IOUtils.IOEnv: the environment variables as a record
fn io_env(_: &Ev, _: &mut Vec<Slot>, _s0: &[Value], _s1: &[Value]) -> R<Value> {
    let mut pairs: Vec<(Value, Value)> = vec![];
    for (k, v) in std::env::vars() {
        pairs.push((Value::str(&k), Value::str(&v)));
    }
    Value::fcn_from(pairs)
}

/// IOUtils.atoi
fn atoi(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    match arg(ev, a, 0, s0, s1)? {
        Value::Str(id) => match intern::name_of(id).trim().parse::<i32>() {
            Ok(n) => Ok(Value::Int(n)),
            Err(_) => fail(format!("For input string: \"{}\"", intern::name_of(id))),
        },
        v => module_arg_err("first", "atoi", "string", &v),
    }
}

// ------------------------------------------------------------------ Graphs / UndirectedGraphs (AbstractGraphs.java)

#[derive(Clone, Copy, PartialEq, Eq)]
enum GMode {
    Forward,
    Transpose,
    Symmetric,
}

struct Graph {
    nodes: Rc<Vec<Value>>,
    /// adjacency lists by node index
    adj: Vec<Vec<usize>>,
}

fn node_index(nodes: &[Value], v: &Value) -> R<Option<usize>> {
    let (mut lo, mut hi) = (0usize, nodes.len());
    while lo < hi {
        let mid = (lo + hi) / 2;
        match nodes[mid].cmp_val(v)? {
            std::cmp::Ordering::Less => lo = mid + 1,
            std::cmp::Ordering::Greater => hi = mid,
            std::cmp::Ordering::Equal => return Ok(Some(mid)),
        }
    }
    Ok(None)
}

fn graph_arg_err<T>(op: &str, pos: &str, kind: &str, detail: &str, v: &Value) -> R<T> {
    fail_code(
        ec::TLC_MODULE_ARGUMENT_ERROR,
        format!("The {} argument of {} should be a {} {}, but instead it is:\n{}", pos, op, kind, detail, crate::pprint::ppr(&v.to_tla())),
    )
}

/// directed edge: a pair `<<a, b>>`; undirected: a set `{a, b}` (a singleton is a self-loop)
fn endpoints(edge: &Value, directed: bool) -> R<Option<(Value, Value)>> {
    if directed {
        return Ok(match edge {
            Value::Tuple(t) if t.len() == 2 => Some((t[0].clone(), t[1].clone())),
            _ => None,
        });
    }
    if !edge.is_set_like() {
        return Ok(None);
    }
    let e = edge.enumerate()?;
    Ok(match e.len() {
        1 => Some((e[0].clone(), e[0].clone())),
        2 => Some((e[0].clone(), e[1].clone())),
        _ => None,
    })
}

fn to_graph(op: &str, pos: &str, kind: &str, v: &Value, directed: bool, mode: GMode) -> R<Graph> {
    let rcd = v.force_fcn()?;
    let (node, edge) = match &rcd {
        Value::Fcn(f) => {
            let (mut n, mut e) = (None, None);
            for (d, x) in f.dom.iter().zip(f.vals.iter()) {
                if let Value::Str(id) = d {
                    match &*intern::name_of(*id) {
                        "node" => n = Some(x.clone()),
                        "edge" => e = Some(x.clone()),
                        _ => {}
                    }
                }
            }
            (n, e)
        }
        _ => (None, None),
    };
    let node = match node {
        Some(n) if n.is_set_like() => n,
        _ => return graph_arg_err(op, pos, kind, "record whose node field is a set", v),
    };
    let edge = match edge {
        Some(e) if e.is_set_like() => e,
        _ => return graph_arg_err(op, pos, kind, "record whose edge field is a set", v),
    };
    let nodes = node.enumerate()?;
    let mut adj: Vec<Vec<usize>> = vec![vec![]; nodes.len()];
    for ed in edge.enumerate()?.iter() {
        if let Some((a, b)) = endpoints(ed, directed)? {
            let (ia, ib) = match (node_index(&nodes, &a)?, node_index(&nodes, &b)?) {
                (Some(x), Some(y)) => (x, y),
                _ => continue,
            };
            let (from, to) = if mode == GMode::Transpose { (ib, ia) } else { (ia, ib) };
            adj[from].push(to);
            if mode == GMode::Symmetric && from != to {
                adj[to].push(from);
            }
        }
    }
    Ok(Graph { nodes, adj })
}

fn reachable(g: &Graph, src: usize) -> Vec<bool> {
    let mut seen = vec![false; g.nodes.len()];
    let mut q = std::collections::VecDeque::new();
    seen[src] = true;
    q.push_back(src);
    while let Some(c) = q.pop_front() {
        for &n in &g.adj[c] {
            if !seen[n] {
                seen[n] = true;
                q.push_back(n);
            }
        }
    }
    seen
}

fn extend_simple_path(g: &Graph, cur: usize, path: &mut Vec<usize>, visited: &mut Vec<bool>, out: &mut Vec<Value>) {
    out.push(Value::tuple(path.iter().map(|&i| g.nodes[i].clone()).collect()));
    for &n in &g.adj[cur] {
        if !visited[n] {
            visited[n] = true;
            path.push(n);
            extend_simple_path(g, n, path, visited, out);
            path.pop();
            visited[n] = false;
        }
    }
}

fn simple_path_impl(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value], kind: &str, directed: bool) -> R<Value> {
    let gv = arg(ev, a, 0, s0, s1)?;
    let mode = if directed { GMode::Forward } else { GMode::Symmetric };
    let g = to_graph("SimplePath", "first", kind, &gv, directed, mode)?;
    let mut out = vec![];
    let mut visited = vec![false; g.nodes.len()];
    for start in 0..g.nodes.len() {
        let mut path = vec![start];
        visited[start] = true;
        extend_simple_path(&g, start, &mut path, &mut visited, &mut out);
        visited[start] = false;
    }
    Value::set_from(out)
}

fn are_connected_in_impl(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value], kind: &str, directed: bool) -> R<Value> {
    let m = arg(ev, a, 0, s0, s1)?;
    let n = arg(ev, a, 1, s0, s1)?;
    let gv = arg(ev, a, 2, s0, s1)?;
    let mode = if directed { GMode::Forward } else { GMode::Symmetric };
    let g = to_graph("AreConnectedIn", "third", kind, &gv, directed, mode)?;
    let (im, inn) = match (node_index(&g.nodes, &m)?, node_index(&g.nodes, &n)?) {
        (Some(x), Some(y)) => (x, y),
        _ => return Ok(Value::Bool(false)),
    };
    if im == inn {
        return Ok(Value::Bool(true));
    }
    Ok(Value::Bool(reachable(&g, im)[inn]))
}

fn graphs_simple_path(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    simple_path_impl(ev, a, s0, s1, "directed graph", true)
}
fn graphs_are_connected_in(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    are_connected_in_impl(ev, a, s0, s1, "directed graph", true)
}
fn ugraphs_simple_path(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    simple_path_impl(ev, a, s0, s1, "undirected graph", false)
}
fn ugraphs_are_connected_in(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    are_connected_in_impl(ev, a, s0, s1, "undirected graph", false)
}

fn graphs_is_strongly_connected(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let gv = arg(ev, a, 0, s0, s1)?;
    let g = to_graph("IsStronglyConnected", "first", "directed graph", &gv, true, GMode::Forward)?;
    if g.nodes.is_empty() {
        return Ok(Value::Bool(true));
    }
    if reachable(&g, 0).iter().any(|&b| !b) {
        return Ok(Value::Bool(false));
    }
    let gt = to_graph("IsStronglyConnected", "first", "directed graph", &gv, true, GMode::Transpose)?;
    Ok(Value::Bool(reachable(&gt, 0).iter().all(|&b| b)))
}

fn ugraphs_connected_components(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let gv = arg(ev, a, 0, s0, s1)?;
    let g = to_graph("ConnectedComponents", "first", "undirected graph", &gv, false, GMode::Symmetric)?;
    let mut done = vec![false; g.nodes.len()];
    let mut comps: Vec<Value> = vec![];
    for i in 0..g.nodes.len() {
        if done[i] {
            continue;
        }
        let seen = reachable(&g, i);
        let mut members = vec![];
        for (j, &b) in seen.iter().enumerate() {
            if b {
                done[j] = true;
                members.push(g.nodes[j].clone());
            }
        }
        comps.push(Value::set_from(members)?);
    }
    Value::set_from(comps)
}


// ------------------------------------------------------------------ Bags (tlc2.module.Bags)

fn bag_parts(b: &Value) -> R<Option<(Vec<Value>, Vec<Value>)>> {
    if !b.is_fcn_like() {
        return Ok(None);
    }
    Ok(b.force_fcn()?.fcn_parts())
}

fn bags_empty(_: &Ev, _: &mut Vec<Slot>, _s0: &[Value], _s1: &[Value]) -> R<Value> {
    Ok(Value::tuple(vec![]))
}

fn is_a_bag_val(b: &Value) -> R<bool> {
    match bag_parts(b)? {
        None => Ok(false),
        Some((_, vals)) => Ok(vals.iter().all(|v| matches!(v, Value::Int(n) if *n > 0))),
    }
}

fn bags_is_a_bag(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let b = arg(ev, a, 0, s0, s1)?;
    Ok(Value::Bool(is_a_bag_val(&b)?))
}

fn bag_apply_err<T>(op: &str, what: &str, v: &Value) -> R<T> {
    fail_code(
        ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE,
        format!("Applying {} to {}, but instead it is:\n{}", op, what, crate::pprint::ppr(&v.to_tla())),
    )
}

fn bags_cardinality(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let b = arg(ev, a, 0, s0, s1)?;
    let (_, vals) = match bag_parts(&b)? {
        Some(p) => p,
        None => return bag_apply_err("BagCardinality", "a function with a finite domain", &b),
    };
    let mut num: i32 = 0;
    for v in vals.iter() {
        match v {
            Value::Int(c) if *c > 0 => {
                num = match num.checked_add(*c) {
                    Some(n) => n,
                    None => return fail_code(ec::TLC_MODULE_OVERFLOW, format!("Overflow when computing {}+{}", num, c)),
                }
            }
            _ => return bag_apply_err("BagCardinality", "a bag", &b),
        }
    }
    Ok(Value::Int(num))
}

fn bags_in(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let e = arg(ev, a, 0, s0, s1)?;
    let b = arg(ev, a, 1, s0, s1)?;
    let (dom, vals) = match bag_parts(&b)? {
        Some(p) => p,
        None => return module_arg_err("second", "BagIn", "bag", &b),
    };
    for (d, v) in dom.iter().zip(vals.iter()) {
        if e.eq_val(d)? {
            return match v {
                Value::Int(n) => Ok(Value::Bool(*n > 0)),
                _ => module_arg_err("second", "BagIn", "bag", &b),
            };
        }
    }
    Ok(Value::Bool(false))
}

fn bags_copies_in(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let e = arg(ev, a, 0, s0, s1)?;
    let b = arg(ev, a, 1, s0, s1)?;
    let (dom, vals) = match bag_parts(&b)? {
        Some(p) => p,
        None => return module_arg_err("second", "CopiesIn", "bag", &b),
    };
    for (d, v) in dom.iter().zip(vals.iter()) {
        if e.eq_val(d)? {
            return match v {
                Value::Int(_) => Ok(v.clone()),
                _ => module_arg_err("second", "CopiesIn", "bag", &b),
            };
        }
    }
    Ok(Value::Int(0))
}

fn bags_cup(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let b1 = arg(ev, a, 0, s0, s1)?;
    let b2 = arg(ev, a, 1, s0, s1)?;
    if !is_a_bag_val(&b1)? {
        return module_arg_err("first", "(+)", "bag", &b1);
    }
    if !is_a_bag_val(&b2)? {
        return module_arg_err("second", "(+)", "bag", &b2);
    }
    let (d1, v1) = bag_parts(&b1)?.unwrap();
    let (d2, v2) = bag_parts(&b2)?.unwrap();
    let mut pairs: Vec<(Value, Value)> = d1.into_iter().zip(v1.into_iter()).collect();
    for (d, v) in d2.into_iter().zip(v2.into_iter()) {
        let mut found = false;
        for p in pairs.iter_mut() {
            if p.0.eq_val(&d)? {
                if let (Value::Int(x), Value::Int(y)) = (&p.1, &v) {
                    p.1 = match x.checked_add(*y) {
                        Some(n) => Value::Int(n),
                        None => return fail_code(ec::TLC_MODULE_OVERFLOW, format!("Overflow when computing {}+{}", x, y)),
                    };
                }
                found = true;
                break;
            }
        }
        if !found {
            pairs.push((d, v));
        }
    }
    Value::fcn_from(pairs)
}

fn bags_diff(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let b1 = arg(ev, a, 0, s0, s1)?;
    let b2 = arg(ev, a, 1, s0, s1)?;
    let (d1, v1) = match bag_parts(&b1)? {
        Some(p) => p,
        None => return module_arg_err("first", "(-)", "bag", &b1),
    };
    let (d2, v2) = match bag_parts(&b2)? {
        Some(p) => p,
        None => return module_arg_err("second", "(-)", "bag", &b2),
    };
    let mut pairs: Vec<(Value, Value)> = vec![];
    for (d, v) in d1.iter().zip(v1.iter()) {
        let mut n = match v {
            Value::Int(n) => *n,
            _ => return module_arg_err("first", "(-)", "bag", &b1),
        };
        for (e, w) in d2.iter().zip(v2.iter()) {
            if d.eq_val(e)? {
                if let Value::Int(m) = w {
                    n -= *m;
                }
                break;
            }
        }
        if n > 0 {
            pairs.push((d.clone(), Value::Int(n)));
        }
    }
    Value::fcn_from(pairs)
}

fn bags_to_set(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let b = arg(ev, a, 0, s0, s1)?;
    match bag_parts(&b)? {
        Some((dom, _)) => Value::set_from(dom),
        None => bag_apply_err("BagToSet", "a function with a finite domain", &b),
    }
}

fn bags_set_to_bag(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0, s0, s1)?;
    if !s.is_set_like() {
        return bag_apply_err("SetToBag", "a finite set", &s);
    }
    let elems = s.enumerate()?;
    Value::fcn_from(elems.iter().map(|e| (e.clone(), Value::Int(1))).collect())
}


/// Java: DyadicRationals.reduce
fn dyadic_reduce(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let v = arg(ev, a, 0, s0, s1)?;
    let (mut num, mut den) = (None, None);
    if let Value::Fcn(f) = &v {
        for (d, x) in f.dom.iter().zip(f.vals.iter()) {
            if let Value::Str(id) = d {
                match &*intern::name_of(*id) {
                    "num" => num = Some(x.clone()),
                    "den" => den = Some(x.clone()),
                    _ => {}
                }
            }
        }
    }
    let (n, d) = match (num, den) {
        (Some(Value::Int(n)), Some(Value::Int(d))) => (n, d),
        _ => {
            return fail_code(
                ec::TLC_MODULE_ONE_ARGUMENT_ERROR,
                format!("The argument of Half should be a record, but instead it is:
{}", crate::pprint::ppr(&v.to_tla())),
            )
        }
    };
    let (mut x, mut y) = (n.unsigned_abs() as u64, d.unsigned_abs() as u64);
    while y != 0 {
        let t = x % y;
        x = y;
        y = t;
    }
    let g = x as i32;
    if g == 1 {
        return Ok(v);
    }
    Ok(Value::record(vec![(intern::intern("den"), Value::Int(d / g)), (intern::intern("num"), Value::Int(n / g))]))
}

// ---------------------------------------------------------------------------------------------- lookup

pub fn lookup(module: &str, name: &str) -> Option<NativeFn> {
    let f: N = match (module, name) {
        ("Naturals", "+") => plus,
        ("Naturals", "-") => minus,
        ("Naturals", "*") => times,
        ("Naturals", "<") => lt,
        ("Naturals", ">") => gt,
        ("Naturals", "\\leq") => le,
        ("Naturals", "\\geq") => ge,
        ("Naturals", "..") => dotdot,
        ("Naturals", "\\div") => intdiv,
        ("Naturals", "%") => modulo,
        ("Naturals", "^") => expt,
        ("Naturals", "Nat") => nat,
        ("Integers", "Int") => int,
        ("Integers", "-.") => uminus,
        ("Reals", "Real") => real,
        ("Sequences", "Seq") => seq_set,
        ("Sequences", "Len") => len,
        ("Sequences", "\\o") => concat,
        ("Sequences", "Append") => append,
        ("Sequences", "Head") => head,
        ("Sequences", "Tail") => tail,
        ("Sequences", "SubSeq") => subseq,
        ("Sequences", "SelectSeq") => select_seq,
        ("FiniteSets", "IsFiniteSet") => is_finite_set,
        ("FiniteSets", "Cardinality") => cardinality,
        ("TLC", "Print") => print,
        ("TLC", "PrintT") => print_t,
        ("TLC", "Assert") => assert_,
        ("TLC", "ToString") => to_string,
        ("TLC", "JavaTime") => java_time,
        ("TLC", ":>") => make_fcn,
        ("TLC", "@@") => combine_fcn,
        ("TLC", "Permutations") => permutations,
        ("TLC", "SortSeq") => sort_seq,
        ("TLC", "RandomElement") => random_element,
        ("TLC", "TLCGet") => tlc_get,
        ("TLC", "TLCSet") => tlc_set,
        ("Functions", "FoldFunctionOnSet") => fold_function_on_set,
        ("Functions", "FoldFunction") => fold_function,
        ("Functions", "IsInjective") => is_injective,
        ("Functions", "AntiFunction") => anti_function,
        ("FiniteSetsExt", "FoldSet") => fold_set,
        ("FiniteSetsExt", "Quantify") => quantify,
        ("IOUtils", "IOEnv") => io_env,
        ("DyadicRationals", "Reduce") => dyadic_reduce,
        ("Bags", "EmptyBag") => bags_empty,
        ("Bags", "IsABag") => bags_is_a_bag,
        ("Bags", "BagCardinality") => bags_cardinality,
        ("Bags", "BagIn") => bags_in,
        ("Bags", "CopiesIn") => bags_copies_in,
        ("Bags", r"\oplus") => bags_cup,
        ("Bags", r"\ominus") => bags_diff,
        ("Bags", "BagToSet") => bags_to_set,
        ("Bags", "SetToBag") => bags_set_to_bag,
        ("Graphs", "SimplePath") => graphs_simple_path,
        ("Graphs", "AreConnectedIn") => graphs_are_connected_in,
        ("Graphs", "IsStronglyConnected") => graphs_is_strongly_connected,
        ("UndirectedGraphs", "SimplePath") => ugraphs_simple_path,
        ("UndirectedGraphs", "AreConnectedIn") => ugraphs_are_connected_in,
        ("UndirectedGraphs", "ConnectedComponents") => ugraphs_connected_components,
        ("IOUtils", "atoi") => atoi,
        _ => return None,
    };
    Some(f)
}
