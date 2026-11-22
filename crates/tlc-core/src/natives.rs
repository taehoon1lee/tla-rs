//! Port of `tlc2.module.*` (Naturals, Integers, Sequences, FiniteSets, TLC, Bags, ...): native implementations that
//! TLC substitutes for the dummy definitions of the standard modules (keyed by module and operator name).

use crate::ec;
use crate::eval::Ev;
use crate::ir::*;
use crate::value::*;
use std::rc::Rc;
use tla_sany::intern;

fn arg(ev: &Ev, a: &mut Vec<Slot>, i: usize) -> R<Value> {
    let s = std::mem::replace(&mut a[i], Slot::Unset);
    ev.force_slot(s)
}

fn int_arg(ev: &Ev, a: &mut Vec<Slot>, i: usize, which: &str, op: &str) -> R<i32> {
    match arg(ev, a, i)? {
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

fn plus(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "+")?;
    let y = int_arg(ev, a, 1, "second", "+")?;
    match x.checked_add(y) {
        Some(r) => Ok(Value::Int(r)),
        None => overflow(format!("{}+{}", x, y)),
    }
}

fn minus(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "-")?;
    let y = int_arg(ev, a, 1, "second", "-")?;
    match x.checked_sub(y) {
        Some(r) => Ok(Value::Int(r)),
        None => overflow(format!("{}-{}", x, y)),
    }
}

fn times(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "*")?;
    let y = int_arg(ev, a, 1, "second", "*")?;
    match x.checked_mul(y) {
        Some(r) => Ok(Value::Int(r)),
        None => overflow(format!("{}*{}", x, y)),
    }
}

fn uminus(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "-")?;
    match x.checked_neg() {
        Some(r) => Ok(Value::Int(r)),
        None => overflow(format!("-{}", x)),
    }
}

fn lt(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "<")?;
    let y = int_arg(ev, a, 1, "second", "<")?;
    Ok(Value::Bool(x < y))
}
fn le(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "<=")?;
    let y = int_arg(ev, a, 1, "second", "<=")?;
    Ok(Value::Bool(x <= y))
}
fn gt(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", ">")?;
    let y = int_arg(ev, a, 1, "second", ">")?;
    Ok(Value::Bool(x > y))
}
fn ge(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", ">=")?;
    let y = int_arg(ev, a, 1, "second", ">=")?;
    Ok(Value::Bool(x >= y))
}

fn dotdot(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = int_arg(ev, a, 0, "first", "..")?;
    let y = int_arg(ev, a, 1, "second", "..")?;
    Ok(Value::Interval(x, y))
}

fn intdiv(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let n1 = int_arg(ev, a, 0, "first", "\\div")?;
    let n2 = int_arg(ev, a, 1, "second", "\\div")?;
    if n2 == 0 {
        return fail_code(ec::TLC_MODULE_DIVISION_BY_ZERO, "The second argument of \\div is 0.");
    }
    let mut q = n1.wrapping_div(n2);
    if q < 0 && q.wrapping_mul(n2) != n1 {
        q -= 1;
    }
    Ok(Value::Int(q))
}

fn modulo(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let n1 = int_arg(ev, a, 0, "first", "%")?;
    let n2 = int_arg(ev, a, 1, "second", "%")?;
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

fn expt(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let m = int_arg(ev, a, 0, "first", "^")?;
    let n = int_arg(ev, a, 1, "second", "^")?;
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

fn nat(_: &Ev, _: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    Ok(Value::NatSet)
}
fn int(_: &Ev, _: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    Ok(Value::IntSet)
}
fn real(_: &Ev, _: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
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

fn seq_set(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0)?;
    Ok(Value::SeqOf(Rc::new(s)))
}

fn len(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let v = arg(ev, a, 0)?;
    Ok(Value::Int(as_seq(&v, "Len")?.len() as i32))
}

fn concat(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0)?;
    let y = arg(ev, a, 1)?;
    let mut s = as_seq(&x, "\\o")?;
    s.extend(as_seq(&y, "\\o")?);
    Ok(Value::tuple(s))
}

fn append(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0)?;
    let e = arg(ev, a, 1)?;
    let mut s = as_seq(&x, "Append")?;
    s.push(e);
    Ok(Value::tuple(s))
}

fn head(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0)?;
    let s = as_seq(&x, "Head")?;
    match s.first() {
        Some(v) => Ok(v.clone()),
        None => fail_code(ec::TLC_MODULE_APPLY_EMPTY_SEQ, "Attempted to apply Head to the empty sequence."),
    }
}

fn tail(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0)?;
    let s = as_seq(&x, "Tail")?;
    if s.is_empty() {
        return fail_code(ec::TLC_MODULE_APPLY_EMPTY_SEQ, "Attempted to apply Tail to the empty sequence.");
    }
    Ok(Value::tuple(s[1..].to_vec()))
}

fn subseq(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0)?;
    let m = int_arg(ev, a, 1, "second", "SubSeq")?;
    let n = int_arg(ev, a, 2, "third", "SubSeq")?;
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
    let x = arg(ev, a, 0)?;
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

fn is_finite_set(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0)?;
    if !s.is_set_like() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR_AN,
            format!("The first argument of IsFiniteSet should be a set, but instead it is:\n{}", s.to_tla()),
        );
    }
    Ok(Value::Bool(s.is_finite()))
}

fn cardinality(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0)?;
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

fn print(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let v1 = arg(ev, a, 0)?.normalize()?;
    let v2 = arg(ev, a, 1)?;
    let n2 = v2.normalize()?;
    ev.out.borrow_mut().push(format!("{}  {}", v1.to_tla(), n2.to_tla()));
    Ok(v2)
}

fn print_t(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let v = arg(ev, a, 0)?.normalize()?;
    ev.out.borrow_mut().push(v.to_tla());
    Ok(Value::Bool(true))
}

fn assert_(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let v1 = arg(ev, a, 0)?;
    if let Value::Bool(true) = v1 {
        return Ok(v1);
    }
    let v2 = std::mem::replace(&mut a[1], Slot::Unset);
    let msg = match ev.force_slot(v2) {
        Ok(v) => match &v {
            Value::Str(id) => intern::name_of(*id).to_string(),
            other => other.to_tla(),
        },
        Err(e) => return Err(e),
    };
    fail_code(ec::TLC_VALUE_ASSERT_FAILED, format!("The first argument of Assert evaluated to FALSE; the second argument was:\n{}", msg))
}

fn to_string(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let v = arg(ev, a, 0)?.normalize()?;
    Ok(Value::str(&v.to_tla()))
}

fn java_time(_: &Ev, _: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
    Ok(Value::Int((t as i32) & 0x7FFF_FFFF))
}

fn make_fcn(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let d = arg(ev, a, 0)?;
    let e = arg(ev, a, 1)?;
    Value::fcn_from(vec![(d, e)])
}

fn combine_fcn(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let f = arg(ev, a, 0)?.force_fcn()?;
    let g = arg(ev, a, 1)?.force_fcn()?;
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

fn permutations(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0)?;
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

fn sort_seq(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0)?;
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

fn tlc_get(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let k = arg(ev, a, 0)?;
    match &k {
        Value::Int(i) => Ok(ev.tlc_registers.borrow().get(i).cloned().unwrap_or(Value::Int(0))),
        Value::Str(id) => {
            let name = intern::name_of(*id);
            match ev.stats.borrow().get(&*name) {
                Some(v) => Ok(v.clone()),
                None => fail_code(ec::TLC_MODULE_TLCGET_UNDEFINED, format!("TLCGet({}) is undefined.", k.to_tla())),
            }
        }
        _ => fail(format!("TLCGet was applied to the unsupported argument {}", k.to_tla())),
    }
}

fn tlc_set(ev: &Ev, a: &mut Vec<Slot>, _: &[Value], _: &[Value]) -> R<Value> {
    let k = arg(ev, a, 0)?;
    let v = arg(ev, a, 1)?;
    if let Value::Int(i) = k {
        ev.tlc_registers.borrow_mut().insert(i, v);
        Ok(Value::Bool(true))
    } else {
        fail(format!("TLCSet was applied to the unsupported argument {}", k.to_tla()))
    }
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
        ("TLC", "TLCGet") => tlc_get,
        ("TLC", "TLCSet") => tlc_set,
        _ => return None,
    };
    Some(f)
}
