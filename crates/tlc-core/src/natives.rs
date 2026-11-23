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
    ev.force_slot(s, s0, s1).map_err(|mut e| {
        e.pass = true;
        e
    })
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


/// Java: `Method.toString()` of the method that overrides the operator `module!name` (`public static <ret> <class>.<method>(<params>)`),
/// for the operators whose Java method rethrows the failures of the values it works on (`MethodValue.eval` wraps them)
pub fn java_signature(module: &str, name: &str) -> Option<String> {
    const V: &str = "tlc2.value.impl.Value";
    let (class, method, ret, nargs): (&str, &str, &str, usize) = match (module, name) {
        ("TLC", "Print") => ("TLC", "Print", V, 2),
        ("TLC", "PrintT") => ("TLC", "PrintT", V, 1),
        ("TLC", "ToString") => ("TLC", "ToString", V, 1),
        ("TLC", "Assert") => ("TLC", "Assert", V, 2),
        ("TLC", ":>") => ("TLC", "MakeFcn", V, 2),
        ("TLC", "@@") => ("TLC", "CombineFcn", V, 2),
        ("TLC", "SortSeq") => ("TLC", "SortSeq", V, 2),
        ("TLC", "Permutations") => ("TLC", "Permutations", V, 1),
        ("TLC", "RandomElement") => ("TLC", "RandomElement", V, 1),
        ("Sequences", "Seq") => ("Sequences", "Seq", V, 1),
        ("Sequences", "Len") => ("Sequences", "Len", "tlc2.value.impl.IntValue", 1),
        ("Sequences", "Head") => ("Sequences", "Head", V, 1),
        ("Sequences", "Tail") => ("Sequences", "Tail", V, 1),
        ("Sequences", "Append") => ("Sequences", "Append", V, 2),
        ("Sequences", "\\o") => ("Sequences", "Concat", V, 2),
        ("Sequences", "SubSeq") => ("Sequences", "SubSeq", V, 3),
        ("Sequences", "SelectSeq") => ("Sequences", "SelectSeq", V, 2),
        ("FiniteSets", "IsFiniteSet") => ("FiniteSets", "IsFiniteSet", "tlc2.value.IBoolValue", 1),
        ("FiniteSets", "Cardinality") => ("FiniteSets", "Cardinality", "tlc2.value.impl.IntValue", 1),
        ("Randomization", "RandomSubset") => ("Randomization", "RandomSubset", V, 2),
        _ => return None,
    };
    Some(format!("public static {} tlc2.module.{}.{}({})", ret, class, method, vec![V; nargs].join(",")))
}

/// Java: `MethodValue.eval`: a failure (`Assert.fail`) inside the Java method of an override is reported as an error of the override
pub fn wrap_override_error(module: &str, name: &str, e: Box<TlcErr>) -> Box<TlcErr> {
    if e.pass || e.not_ported || e.code != ec::GENERAL {
        return e;
    }
    match java_signature(module, name) {
        Some(sig) => match override_error::<()>(&sig, &e.msg) {
            Err(mut w) => {
                w.frames = e.frames.clone();
                w
            }
            Ok(()) => e,
        },
        None => e,
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
    // Java: `Naturals.GEQ` reports its failures as `>` (copy and paste in the original)
    let x = int_arg(ev, a, 0, "first", ">", s0, s1)?;
    let y = int_arg(ev, a, 1, "second", ">", s0, s1)?;
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

/// the elements of a sequence without copying them (the `Rc` of the tuple is shared)
fn as_seq_rc(v: &Value, who: &str) -> R<Rc<Vec<Value>>> {
    match v {
        Value::Tuple(t) => Ok(t.clone()),
        Value::FcnLam(_) => match v.force_fcn()? {
            Value::Tuple(t) => Ok(t),
            other => fail_code(
                ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE,
                format!("Applying {} to the following value,
which is not a sequence:
{}", who, other.to_tla()),
            ),
        },
        _ => fail_code(
            ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE,
            format!("Applying {} to the following value,
which is not a sequence:
{}", who, v.to_tla()),
        ),
    }
}

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
    len1(&v)
}

fn len1(v: &Value) -> R<Value> {
    if let Value::Tuple(t) = v {
        return Ok(Value::Int(t.len() as i32));
    }
    // Java: Sequences.Len accepts a string (its length in UTF-16 code units)
    if let Value::Str(id) = v {
        return Ok(Value::Int(intern::name_of(*id).encode_utf16().count() as i32));
    }
    Ok(Value::Int(as_seq_rc(v, "Len")?.len() as i32))
}

// Java: Sequences.Concat (strings concatenate with strings, sequences with sequences)
fn concat(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let y = arg(ev, a, 1, s0, s1)?;
    let evaluating = |form: &str, what: &str, v: &Value| -> R<Value> {
        fail_code(
            ec::TLC_MODULE_EVALUATING,
            format!("Evaluating an expression of the form {} when s is not a {}:\n{}", form, what, crate::pprint::ppr(&v.to_tla())),
        )
    };
    if let Value::Str(i1) = &x {
        return match &y {
            Value::Str(i2) => {
                let (u1, u2) = (intern::name_of(*i1), intern::name_of(*i2));
                Ok(Value::str(&format!("{}{}", u1, u2)))
            }
            _ => evaluating(r"t \o s", "string", &y),
        };
    }
    let seq_of = |v: &Value| -> R<Option<Vec<Value>>> {
        Ok(match v {
            Value::Tuple(t) => Some(t.to_vec()),
            Value::FcnLam(_) => match v.force_fcn()? {
                Value::Tuple(t) => Some(t.to_vec()),
                _ => None,
            },
            _ => None,
        })
    };
    let mut s = match seq_of(&x)? {
        Some(s) => s,
        None => return evaluating(r"s \o t", "sequence", &x),
    };
    match seq_of(&y)? {
        Some(t) => s.extend(t),
        None => return evaluating(r"t \o s", "sequence", &y),
    }
    Ok(Value::tuple(s))
}

fn append(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let e = arg(ev, a, 1, s0, s1)?;
    append2(&x, &e)
}

fn append2(x: &Value, e: &Value) -> R<Value> {
    let t = as_seq_rc(x, "Append")?;
    let mut s = Vec::with_capacity(t.len() + 1);
    s.extend_from_slice(&t);
    s.push(e.clone());
    Ok(Value::tuple(s))
}

fn head(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    head1(&x)
}

fn head1(x: &Value) -> R<Value> {
    let s = as_seq_rc(x, "Head")?;
    match s.first() {
        Some(v) => Ok(v.clone()),
        None => fail_code(ec::TLC_MODULE_APPLY_EMPTY_SEQ, "Attempted to apply Head to the empty sequence."),
    }
}

fn tail(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    tail1(&x)
}

fn tail1(x: &Value) -> R<Value> {
    let s = as_seq_rc(x, "Tail")?;
    if s.is_empty() {
        return fail_code(ec::TLC_MODULE_APPLY_EMPTY_SEQ, "Attempted to apply Tail to the empty sequence.");
    }
    Ok(Value::tuple(s[1..].to_vec()))
}

fn subseq(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let x = arg(ev, a, 0, s0, s1)?;
    let m = int_arg(ev, a, 1, "second", "SubSeq", s0, s1)?;
    let n = int_arg(ev, a, 2, "third", "SubSeq", s0, s1)?;
    let s = as_seq_rc(&x, "SubSeq")?;
    if n < m {
        return Ok(Value::tuple(vec![]));
    }
    if m < 1 || (m as usize) > s.len() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN,
            format!(
                "The second argument of SubSeq must be in the domain of its first argument:\n{}\n, but instead it is\n{}",
                Value::Tuple(s.clone()).to_tla(),
                m
            ),
        );
    }
    if (n as usize) > s.len() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN,
            format!(
                "The third argument of SubSeq must be in the domain of its first argument:\n{}\n, but instead it is\n{}",
                Value::Tuple(s.clone()).to_tla(),
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
    // Java: the override wraps the failure of `Value.isFinite()` (`{x \in S : p(x)}` with an S TLC cannot classify)
    match is_finite_chk(&s) {
        Ok(b) => Ok(Value::Bool(b)),
        Err(e) => override_error(
            "public static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value)",
            &e.msg,
        ),
    }
}

/// `Value.isFinite()` as Java computes it: a set of the form `{x \in S : p(x)}` is finite when S is; if TLC cannot tell, it fails
fn is_finite_chk(v: &Value) -> R<bool> {
    match v {
        Value::SetPred(p) => {
            if !is_finite_chk(&p.base)? {
                return fail(format!(
                    "Attempted to check if expression of form {{x \\in S : p(x)}} is a finite set, but cannot check if S:\n{}\nis finite.",
                    v_ppr(&p.base)
                ));
            }
            Ok(true)
        }
        Value::SetCup(p) => Ok(is_finite_chk(&p.0)? && is_finite_chk(&p.1)?),
        Value::SetCap(p) => Ok(is_finite_chk(&p.0)? || is_finite_chk(&p.1)?),
        Value::SetDiff(p) => is_finite_chk(&p.0),
        Value::Subset(s) => is_finite_chk(s),
        Value::KSubset(p) => Ok(p.0 <= 0 || is_finite_chk(&p.1)?),
        other => Ok(other.is_finite()),
    }
}

fn v_ppr(v: &Value) -> String {
    crate::pprint::ppr(&v.to_tla())
}

fn cardinality(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0, s0, s1)?;
    cardinality1(&s)
}

fn cardinality1(s: &Value) -> R<Value> {
    if let Value::Set(v) = s {
        return Ok(Value::Int(v.len() as i32));
    }
    if !s.is_set_like() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR_AN,
            format!("The first argument of Cardinality should be a set, but instead it is:
{}", s.to_tla()),
        );
    }
    if !s.is_finite() && !matches!(s, Value::KSubset(_)) {
        return fail_code(ec::TLC_MODULE_COMPUTING_CARDINALITY, format!("Attempted to compute cardinality of the value
{}", s.to_tla()));
    }
    let n = match s.size() {
        Ok(n) => n,
        // Java: a runtime exception of the override (`k=32 and n=64`) is wrapped by MethodValue.eval
        Err(e) if e.code == JAVA_RUNTIME_EXCEPTION => {
            return override_error("public static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value)", &e.msg)
        }
        Err(e) => return Err(e),
    };
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
        // Java: `Values.ppr(v2.toString())`: a string is shown with its quotes
        Ok(v) => crate::pprint::ppr(&v.to_tla()),
        Err(e) => return Err(e),
    };
    fail_code(ec::TLC_VALUE_ASSERT_FAILED, format!("The first argument of Assert evaluated to FALSE; the second argument was:\n{}", msg))
}

fn to_string(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    // Java: `v.toStringUnchecked()`: a product-like set is printed by its structure when it is too big to expand
    let v = arg(ev, a, 0, s0, s1)?;
    // Java: `toStringUnchecked` does not swallow the failure of the size test of a product-like set
    v.expand_size()?;
    if let Value::KSubset(_) = &v {
        if let Err(e) = v.size() {
            if e.code == JAVA_RUNTIME_EXCEPTION {
                return override_error("public static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value)", &e.msg);
            }
        }
    }
    let v = if matches!(v, Value::SetOfRcds(_) | Value::SetOfFcns(_) | Value::SetOfTuples(_) | Value::KSubset(_)) { v } else { v.normalize()? };
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

/// Java: `RandomEnumerableValues.get()`: the generator of the running thread.  In the scope of the next-state relation it is seeded
/// with the fingerprint of the predecessor state XOR the seed, once per state (`TLCStateRandom.initialize`); elsewhere (the assumptions,
/// the initial states) one generator seeded with the seed serves all calls.
fn with_rng<T>(ev: &Ev, f: impl FnOnce(&mut crate::jrandom::JRandom) -> T) -> T {
    if let Some(vals) = &*ev.pred_state.borrow() {
        let mut w = ev.wrng.borrow_mut();
        let g = w.get_or_insert_with(|| crate::jrandom::JRandom::new(ev.seed.get()));
        if ev.rng_for.get() != ev.pred_id.get() {
            let fp = crate::jfp::fp64(ev.fp_index.get()).state(vals);
            g.set_seed((fp as i64) ^ ev.seed.get());
            ev.rng_for.set(ev.pred_id.get());
        }
        return f(g);
    }
    let mut g = ev.rng.borrow_mut();
    f(g.get_or_insert_with(|| crate::jrandom::JRandom::new(ev.seed.get())))
}

/// the next pseudo-random double of the shared generator (Java: `RandomEnumerableValues.get().nextDouble()`)
fn next_double(ev: &Ev) -> f64 {
    with_rng(ev, |g| g.next_double())
}

/// Java: `EnumerableValue.computeOptimalMandA`: the modulus and the multiplier of the linear congruential generator that visits
/// every index of a set of `size` elements
fn optimal_m_and_a(size: i64) -> (i64, i64) {
    fn prime_factors(mut n: i64) -> Vec<i64> {
        let mut out = vec![];
        let mut p = 2i64;
        while p * p <= n {
            while n % p == 0 {
                out.push(p);
                n /= p;
            }
            p += if p == 2 { 1 } else { 2 };
        }
        if n > 1 {
            out.push(n);
        }
        out
    }
    fn distinct(f: &[i64]) -> Vec<i64> {
        let mut d: Vec<i64> = vec![];
        for p in f {
            if !d.contains(p) {
                d.push(*p);
            }
        }
        d
    }
    let mut n = size.max(9);
    let mut f = prime_factors(n);
    while n % 4 == 0 || distinct(&f).len() == f.len() {
        n += 1;
        f = prime_factors(n);
    }
    let mut a: i64 = 1;
    for p in distinct(&f) {
        a *= p;
    }
    (n, a + 1)
}

// Java: TLC.RandomElement
fn random_element_of(ev: &Ev, v: &Value) -> R<Value> {
    let wrong = || {
        fail_code(
            ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE,
            format!(
                "Applying RandomElement to the following value,\nwhich is not a finite set:\n{}",
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
                // Java: `TLCGlobals.mainChecker` is null while the spec is processed: all but "duration" are undefined
                if ev.setup_phase.get() && (1..=4).contains(&i) {
                    return fail_code(ec::TLC_MODULE_TLCGET_UNDEFINED, format!("TLCGet({}) was undefined.", name));
                }
                let mut v = ev.counters.get()[i];
                if i == 0 {
                    // Java: the level of the successor state under a prime
                    v += ev.prime_depth.get() as i64;
                }
                return match i32::try_from(v) {
                    Ok(n) => Ok(Value::Int(n)),
                    Err(_) => fail_code(ec::TLC_MODULE_OVERFLOW, format!("Overflow when computing {}", v)),
                };
            }
            // Java: TLCGetSet.TLCGet("-Dname"): `System.getProperty(name, "-Dname")`; no JVM properties are set here
            if name.starts_with("-D") {
                return Ok(Value::Str(*id));
            }
            // Java: TLCGetSet.TLCGet: "all" / "all:named" give the register values of every worker (there is one)
            if &*name == "all" {
                let regs = ev.tlc_registers.borrow();
                let mut keys: Vec<i32> = regs.keys().copied().collect();
                keys.sort_unstable();
                let pairs = keys.into_iter().map(|i| (Value::Int(i), Value::tuple(vec![regs[&i].clone()]))).collect();
                return Value::fcn_from(pairs);
            }
            if &*name == "all:named" {
                let pairs = ev
                    .named_regs
                    .borrow()
                    .iter()
                    .map(|(k, v)| (Value::str(k), Value::tuple(vec![v.clone()])))
                    .collect();
                return Value::fcn_from(pairs);
            }
            if name.starts_with("s:") {
                return match ev.named_regs.borrow().get(&*name) {
                    Some(v) => Ok(v.clone()),
                    None => fail_code(ec::TLC_MODULE_TLCGET_UNDEFINED, format!("TLCGet({}) is undefined.", name)),
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
    } else if let Value::Str(id) = &k {
        // Java: TLCGetSet.TLCSet: named registers ("s:" prefix) are kept per worker
        let name = intern::name_of(*id);
        if name.starts_with("s:") {
            ev.named_regs.borrow_mut().insert(name.to_string(), v);
            return Ok(Value::Bool(true));
        }
        fail(format!("TLCSet was applied to the unsupported argument {}", k.to_tla()))
    } else {
        fail(format!("TLCSet was applied to the unsupported argument {}", k.to_tla()))
    }
}

// ------------------------------------------------------------------ Randomization (tlc2.module.Randomization)

/// a constituent set of a product-like set: its elements, without enumerating a big interval
struct Cons {
    vals: Option<Rc<Vec<Value>>>,
    lo: i64,
    n: u64,
}

impl Cons {
    fn of(s: &Value) -> R<Cons> {
        match s {
            Value::Interval(lo, hi) => Ok(Cons { vals: None, lo: *lo as i64, n: if hi < lo { 0 } else { (*hi as i64 - *lo as i64 + 1) as u64 } }),
            other => {
                let v = other.enumerate()?;
                let n = v.len() as u64;
                Ok(Cons { vals: Some(v), lo: 0, n })
            }
        }
    }
    fn get(&self, i: u64) -> Value {
        match &self.vals {
            Some(v) => v[i as usize].clone(),
            None => Value::Int((self.lo + i as i64) as i32),
        }
    }
}

/// how an element of a product-like set is built from one element of each constituent
enum ProductKind {
    Tuple,
    Fcn(Vec<Value>),
    Rcd(Vec<u32>),
}

/// Java: the indices `SubsetEnumerator` (`EnumerableValue`) / `BigIntegerSubsetEnumerator` (`SetOfFcnsOrRcdsValue`) yield for
/// `RandomSubset(k, S)` with `n` elements (a set without elements draws nothing)
fn pick_indices(ev: &Ev, n: u128, k: u128) -> Vec<u128> {
    if n == 0 {
        return vec![];
    }
    with_rng(ev, |rng| {
        if n > i32::MAX as u128 {
            let a = rng.next_long().wrapping_abs() as i128;
            let x = (i64::MAX - 24) as i128;
            let mut out = Vec::new();
            for i in 0..k {
                out.push((x * i as i128 + a).rem_euclid(n as i128) as u128);
            }
            return out;
        }
        let n = n as i64;
        let (m, a) = optimal_m_and_a(n);
        let mut index = rng.next_int(n as i32) as i64;
        let c = rng.next_prime() as i64;
        // the first n indices the generator yields are all different: later ones repeat them
        let take = k.min(n as u128) as usize;
        let mut out = Vec::with_capacity(take);
        for _ in 0..take {
            loop {
                index = a.wrapping_mul(index).wrapping_add(c) % m;
                if index < n {
                    break;
                }
            }
            out.push(index as u128);
        }
        out
    })
}

/// Java: `Randomization.RandomSubset(k, S)`: `k` distinct elements of the finite set `S`, chosen by index so that a product or a set of
/// functions with 10^9 elements is not enumerated
fn random_subset(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let kv = arg(ev, a, 0, s0, s1)?;
    let s = arg(ev, a, 1, s0, s1)?;
    let k = match kv {
        Value::Int(k) => k,
        v => {
            return fail_code(
                ec::TLC_MODULE_ARGUMENT_ERROR,
                format!("The first argument of RandomSubset should be a nonnegative integer, but instead it is:\n{}", v.to_tla()),
            )
        }
    };
    if !s.is_set_like() || !s.is_finite() {
        return fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR,
            format!("The second argument of RandomSubset should be a finite set, but instead it is:\n{}", s.to_tla()),
        );
    }
    // Java: an empty set has nothing to pick (and draws nothing); its emptiness is decided without enumerating the arguments
    if s.is_empty_set()? {
        return Value::set_from(vec![]);
    }
    let k = k.max(0) as u128;
    let parts = match &s {
        Value::SetOfTuples(ss) => {
            let mut c = Vec::with_capacity(ss.len());
            for x in ss.iter() {
                c.push(Cons::of(x)?);
            }
            Some((c, ProductKind::Tuple))
        }
        Value::SetOfRcds(fs) => {
            let mut c = Vec::with_capacity(fs.len());
            for (_, x) in fs.iter() {
                c.push(Cons::of(x)?);
            }
            Some((c, ProductKind::Rcd(fs.iter().map(|(n, _)| *n).collect())))
        }
        Value::SetOfFcns(p) => {
            let dom = p.0.enumerate()?;
            let mut c = Vec::with_capacity(dom.len());
            for _ in 0..dom.len() {
                c.push(Cons::of(&p.1)?);
            }
            Some((c, ProductKind::Fcn(dom.to_vec())))
        }
        _ => None,
    };
    match parts {
        Some((cons, kind)) => {
            let mut n: u128 = 1;
            for c in cons.iter() {
                n = n.saturating_mul(c.n as u128);
            }
            let mut out = Vec::new();
            for mut idx in pick_indices(ev, n, k) {
                // the last constituent varies fastest
                let mut digits = vec![0u64; cons.len()];
                for i in (0..cons.len()).rev() {
                    let m = cons[i].n.max(1) as u128;
                    digits[i] = (idx % m) as u64;
                    idx /= m;
                }
                let vals: Vec<Value> = cons.iter().zip(digits.iter()).map(|(c, d)| c.get(*d)).collect();
                out.push(match &kind {
                    ProductKind::Tuple => Value::tuple(vals),
                    ProductKind::Fcn(dom) => Value::fcn_from(dom.iter().cloned().zip(vals.into_iter()).collect())?,
                    ProductKind::Rcd(names) => Value::fcn_from(names.iter().map(|n| Value::Str(*n)).zip(vals.into_iter()).collect())?,
                });
            }
            Value::set_from(out)
        }
        None => {
            let c = Cons::of(&s)?;
            let out: Vec<Value> = pick_indices(ev, c.n as u128, k).into_iter().map(|i| c.get(i as u64)).collect();
            Value::set_from(out)
        }
    }
}

/// Java: TLCExt!CounterExample (an `@Evaluation`): the counterexample the POSTCONDITION is checked against; `TRUE` elsewhere
fn counter_example(ev: &Ev, _a: &mut Vec<Slot>, _s0: &[Value], _s1: &[Value]) -> R<Value> {
    Ok(ev.counter_example.borrow().clone().unwrap_or(Value::Bool(true)))
}

/// Java: TLCExt!Trace (an `@Evaluation`): the behavior up to the state an ALIAS is evaluated for
fn ext_trace(ev: &Ev, _a: &mut Vec<Slot>, _s0: &[Value], _s1: &[Value]) -> R<Value> {
    match &*ev.alias_trace.borrow() {
        Some(t) => Ok(Value::tuple(t.clone())),
        None => Ok(Value::Bool(true)),
    }
}

/// Java: TLCExt.lassoOrdinal (`ToTrace`): the states of a counterexample as a sequence, ordered by state number
fn to_trace(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let ce = arg(ev, a, 0, s0, s1)?;
    let states = match ce.force_fcn()?.fcn_parts() {
        Some((d, v)) => d.iter().position(|k| matches!(k, Value::Str(id) if &*intern::name_of(*id) == "state")).map(|i| v[i].clone()),
        None => None,
    };
    let states = match states {
        Some(x) => x,
        None => {
            return fail_code(
                ec::TLC_MODULE_ONE_ARGUMENT_ERROR,
                format!("The argument of ToTrace should be a CounterExample, but instead it is:\n{}", crate::pprint::ppr(&ce.to_tla())),
            )
        }
    };
    let elems = states.enumerate()?;
    let mut out: Vec<Value> = vec![Value::Undef; elems.len()];
    for e in elems.iter() {
        if let Value::Tuple(t) = e {
            if let (Some(Value::Int(n)), Some(rec)) = (t.get(0), t.get(1)) {
                if *n >= 1 && (*n as usize) <= out.len() {
                    out[*n as usize - 1] = rec.clone();
                }
            }
        }
    }
    Ok(Value::tuple(out))
}

/// Java: TLCExt.tlcModelValue: `ModelValue.add(str)`
fn tlc_model_value(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    match arg(ev, a, 0, s0, s1)? {
        Value::Str(id) => Ok(Value::Model(id)),
        v => fail_code(
            ec::TLC_MODULE_ARGUMENT_ERROR,
            format!("The argument of ModelValue should be a string, but instead it is:\n{}", v.to_tla()),
        ),
    }
}

/// Java: TLCExt.assertError (an `@Evaluation`): TRUE iff evaluating the second argument fails with exactly the message the first one
/// names; FALSE when it succeeds or fails differently
fn assert_error(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let err = arg(ev, a, 0, s0, s1)?;
    let expected = match &err {
        Value::Str(id) => intern::name_of(*id).to_string(),
        other => {
            return fail(format!(
                "In computing AssertError, a non-string expression ({}) was used as the err of an AssertError(err, exp).",
                other.to_tla()
            ))
        }
    };
    match arg(ev, a, 1, s0, s1) {
        Ok(_) => Ok(Value::Bool(false)),
        Err(e) if e.not_ported => Err(e),
        Err(e) => {
            // Java: `EvalException(code, params)` / `Assert.fail(code, params)` build the message with `MP.getMessage`, which wraps it in
            // tool-mode markers; only `Assert.fail(String)` (EC.GENERAL) leaves the plain text
            let java_text = if e.code == ec::GENERAL || e.msg.starts_with("@!@!@STARTMSG") || e.code < 0 {
                e.msg.clone()
            } else {
                format!("@!@!@STARTMSG {}:0 @!@!@\n{}\n@!@!@ENDMSG {} @!@!@", e.code, e.msg, e.code)
            };
            Ok(Value::Bool(java_text == expected))
        }
    }
}

/// Java: TLCExt.tlcFingerprint: the fingerprint of the (normalized) value, cut down to an int
fn tlc_fp(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let v = arg(ev, a, 0, s0, s1)?.normalize()?;
    let mut h = Hasher::new();
    v.hash_into(&mut h)?;
    Ok(Value::Int(h.finish() as u32 as i32))
}

/// Java: TLCExt.tlcGetOrDefault
fn tlc_get_or_default(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let k = arg(ev, a, 0, s0, s1)?;
    let def = arg(ev, a, 1, s0, s1)?;
    Ok(match &k {
        Value::Int(i) => ev.tlc_registers.borrow().get(i).cloned().unwrap_or(def),
        Value::Str(id) => {
            let name = intern::name_of(*id);
            if name.starts_with("s:") {
                ev.named_regs.borrow().get(&*name).cloned().unwrap_or(def)
            } else {
                def
            }
        }
        _ => def,
    })
}

/// Java: tlc2.module._Possible.counts: the per-name counts of `_Track`, summed over the workers
fn possible_counts(ev: &Ev, _a: &mut Vec<Slot>, _s0: &[Value], _s1: &[Value]) -> R<Value> {
    let rec = ev.named_regs.borrow().get("s:_possible").cloned();
    let mut totals: Vec<(Value, i32)> = Vec::new();
    if let Some(rec) = rec {
        if let Some((dom, vals)) = rec.fcn_parts() {
            for (d, v) in dom.into_iter().zip(vals.into_iter()) {
                let n = match v {
                    Value::Int(n) => n,
                    _ => return fail("Java ClassCastException: a _Possible count is not an integer"),
                };
                let mut found = false;
                for t in totals.iter_mut() {
                    if t.0.cmp_val(&d)? == std::cmp::Ordering::Equal {
                        t.1 = t.1.wrapping_add(n);
                        found = true;
                        break;
                    }
                }
                if !found {
                    totals.push((d, n));
                }
            }
        }
    }
    Value::fcn_from(totals.into_iter().map(|(d, n)| (d, Value::Int(n))).collect())
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

/// Java: FiniteSetsExt.kSubset
fn k_subset(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let kv = arg(ev, a, 0, s0, s1)?;
    let Value::Int(k) = kv else { return module_arg_err("first", "kSubset", "natural number", &kv) };
    let set = arg(ev, a, 1, s0, s1)?;
    if !set.is_set_like() {
        return module_arg_err("second", "kSubset", "set", &set);
    }
    Ok(Value::ksubset(k, set))
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

fn str_of(v: &Value, what: &str) -> R<std::sync::Arc<str>> {
    match v {
        Value::Str(id) => Ok(intern::name_of(*id)),
        _ => fail(format!("{} is not a string: {}", what, v.to_tla())),
    }
}

fn field(v: &Value, name: &str) -> R<Value> {
    v.apply(&Value::str(name))
}

/// the elements of a record, function or tuple in domain order
fn components(v: &Value) -> R<Vec<Value>> {
    let f = if matches!(v, Value::FcnLam(_)) { v.force_fcn()? } else { v.clone() };
    match f.fcn_parts() {
        Some((_, vals)) => Ok(vals),
        None => fail(format!("Was unable to convert element to a tuple or (function) record: {}", v.to_tla())),
    }
}

// Java: tlc2.overrides.SVG.SVGElemToString
fn svg_elem(elem: &Value) -> R<String> {
    let rec = if matches!(elem, Value::FcnLam(_)) { elem.force_fcn()? } else { elem.clone() };
    let is_rec = matches!(&rec, Value::Fcn(f) if f.dom.iter().all(|d| matches!(d, Value::Str(_))));
    if !is_rec {
        return fail(format!("An SVG element must be a record. Value given is of type: {}", elem.to_tla()));
    }
    let name = str_of(&field(&rec, "name")?, "name")?;
    let attrs_v = field(&rec, "attrs")?;
    let attrs = if matches!(attrs_v, Value::FcnLam(_)) { attrs_v.force_fcn()? } else { attrs_v.clone() };
    let mut attr_str = String::new();
    match attrs.fcn_parts() {
        Some((dom, vals)) => {
            for (k, v) in dom.iter().zip(vals.iter()) {
                attr_str.push(' ');
                attr_str.push_str(&str_of(k, "attribute name")?.replace('_', "-"));
                attr_str.push('=');
                attr_str.push('\'');
                attr_str.push_str(&str_of(v, "attribute value")?);
                attr_str.push('\'');
            }
        }
        None => return fail(format!("Was unable to convert element to a record: {}", attrs_v.to_tla())),
    }
    let mut child_str = String::new();
    for c in components(&field(&rec, "children")?)? {
        child_str.push_str(&svg_elem(&c)?);
    }
    let inner = str_of(&field(&rec, "innerText")?, "innerText")?.replace("<<", "&lt;&lt;").replace(">>", "&gt;&gt;");
    Ok(format!("<{}{}>{}{}</{}>", name, attr_str, inner, child_str, name))
}

fn svg_elem_to_string(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let e = arg(ev, a, 0, s0, s1)?;
    Ok(Value::str(&svg_elem(&e)?))
}

fn exec_record(code: i32, out: &str, err: &str) -> Value {
    Value::record(vec![
        (intern::intern("exitValue"), Value::Int(code)),
        (intern::intern("stdout"), Value::str(out)),
        (intern::intern("stderr"), Value::str(err)),
    ])
}

// Java: tlc2.overrides.IOUtils.textSerialize (format "TXT"): writes the string and returns the exit record
fn io_serialize(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let invalid = "Serialize error invalid parameters: ";
    let opts = arg(ev, a, 2, s0, s1)?;
    let format = match field(&opts, "format") {
        Ok(f) => f,
        Err(e) => return Ok(exec_record(1, "", &format!("{}{}", invalid, e.msg))),
    };
    if str_of(&format, "format").map_or(true, |f| &*f != "TXT") {
        return fail("Serialize: unsupported serializer format");
    }
    let parsed = (|| -> R<(std::sync::Arc<str>, std::sync::Arc<str>, Vec<std::sync::Arc<str>>)> {
        let payload = str_of(&arg(ev, a, 0, s0, s1)?, "payload")?;
        let path = str_of(&arg(ev, a, 1, s0, s1)?, "filepath")?;
        let mut options = vec![];
        for o in components(&field(&opts, "openOptions")?)? {
            options.push(str_of(&o, "open option")?);
        }
        str_of(&field(&opts, "charset")?, "charset")?;
        Ok((payload, path, options))
    })();
    let (payload, path, options) = match parsed {
        Ok(p) => p,
        Err(e) => return Ok(exec_record(1, "", &format!("{}{}", invalid, e.msg))),
    };
    let mut oo = std::fs::OpenOptions::new();
    oo.write(true);
    if options.is_empty() {
        oo.create(true).truncate(true);
    }
    for o in &options {
        match &**o {
            "WRITE" => {}
            "APPEND" => {
                oo.append(true);
            }
            "TRUNCATE_EXISTING" => {
                oo.truncate(true);
            }
            "CREATE" => {
                oo.create(true);
            }
            "CREATE_NEW" => {
                oo.create_new(true);
            }
            "READ" | "DELETE_ON_CLOSE" | "SPARSE" | "SYNC" | "DSYNC" => {}
            other => {
                return Ok(exec_record(
                    1,
                    "",
                    &format!(
                        "Serialize error writing to the file: java.lang.IllegalArgumentException: No enum constant java.nio.file.StandardOpenOption.{}",
                        other
                    ),
                ))
            }
        }
    }
    use std::io::Write;
    match oo.open(&*path).and_then(|mut f| f.write_all(payload.as_bytes())) {
        Ok(()) => Ok(exec_record(0, "Finish writing to the file with success!", "")),
        Err(e) => Ok(exec_record(1, "", &format!("Serialize error writing to the file: {}", e))),
    }
}

// Java: tlc2.overrides.SequencesExt.SetToSeq: the elements in normalized order as a sequence
fn set_to_seq(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let s = arg(ev, a, 0, s0, s1)?;
    if !s.is_set_like() || matches!(s, Value::NatSet | Value::IntSet | Value::RealSet | Value::StringSet | Value::SeqOf(_)) {
        return fail_code(
            ec::TLC_MODULE_APPLYING_TO_WRONG_VALUE,
            format!("Applying SetToSeq to the following value,\nwhich is not a finite set:\n{}", crate::pprint::ppr(&s.to_tla())),
        );
    }
    Ok(Value::tuple(s.enumerate()?.to_vec()))
}

// ---------------------------------------------------------------------------------------------- Json (tlc2.overrides.Json)

/// Java: `MethodValue` wraps an exception of an operator override into `TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE`; the text
/// is built with `MP.getMessage`, hence it carries the tool-mode message framing.
fn override_error<T>(signature: &str, msg: &str) -> R<T> {
    fail_code(
        ec::TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE,
        format!(
            "@!@!@STARTMSG 2154:0 @!@!@\nAttempted to apply the operator overridden by the Java method\n{},\nbut it produced the following error:\n{}\n@!@!@ENDMSG 2154 @!@!@",
            signature, msg
        ),
    )
}

/// Java: `FileNotFoundException.getMessage()` of `new FileReader(new File(path))`: `<path> (<OS message>)`
fn file_not_found_message(path: &str, e: &std::io::Error) -> String {
    let shown = if cfg!(windows) { path.replace('/', "\\") } else { path.to_string() };
    let full = e.to_string();
    // strip Rust's " (os error N)" suffix and, like the JDK, one final '.'
    let os = match full.rfind(" (os error") {
        Some(i) => &full[..i],
        None => &full[..],
    };
    let os = os.trim_end();
    let os = os.strip_suffix('.').unwrap_or(os);
    format!("{} ({})", shown, os)
}

enum Json {
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
    Str(String),
    Num(f64),
    Bool(bool),
    Null,
}

/// a lenient JSON reader (Gson `JsonParser.parseString`)
struct JsonReader<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> JsonReader<'a> {
    fn ws(&mut self) {
        while self.i < self.s.len() && (self.s[self.i] as char).is_whitespace() {
            self.i += 1;
        }
    }
    fn err<T>(&self, what: &str) -> Result<T, String> {
        Err(format!("{} at character {}", what, self.i))
    }
    fn value(&mut self) -> Result<Json, String> {
        self.ws();
        match self.s.get(self.i) {
            None => self.err("End of input"),
            Some(b'{') => {
                self.i += 1;
                let mut fields = vec![];
                loop {
                    self.ws();
                    match self.s.get(self.i) {
                        Some(b'}') => {
                            self.i += 1;
                            return Ok(Json::Obj(fields));
                        }
                        Some(b',') => {
                            self.i += 1;
                        }
                        Some(b'"') | Some(b'\'') => {
                            let k = self.string()?;
                            self.ws();
                            if self.s.get(self.i) != Some(&b':') {
                                return self.err("Expected ':'");
                            }
                            self.i += 1;
                            let v = self.value()?;
                            fields.push((k, v));
                        }
                        _ => return self.err("Expected name"),
                    }
                }
            }
            Some(b'[') => {
                self.i += 1;
                let mut items = vec![];
                loop {
                    self.ws();
                    match self.s.get(self.i) {
                        Some(b']') => {
                            self.i += 1;
                            return Ok(Json::Arr(items));
                        }
                        Some(b',') => {
                            self.i += 1;
                        }
                        None => return self.err("End of input"),
                        _ => items.push(self.value()?),
                    }
                }
            }
            Some(b'"') | Some(b'\'') => Ok(Json::Str(self.string()?)),
            Some(_) => {
                let st = self.i;
                while self.i < self.s.len() && !matches!(self.s[self.i], b',' | b']' | b'}' | b':') && !(self.s[self.i] as char).is_whitespace() {
                    self.i += 1;
                }
                let t = std::str::from_utf8(&self.s[st..self.i]).unwrap_or("");
                match t {
                    "true" => Ok(Json::Bool(true)),
                    "false" => Ok(Json::Bool(false)),
                    "null" => Ok(Json::Null),
                    _ => match t.parse::<f64>() {
                        Ok(n) => Ok(Json::Num(n)),
                        Err(_) => Ok(Json::Str(t.to_string())),
                    },
                }
            }
        }
    }
    fn string(&mut self) -> Result<String, String> {
        let q = self.s[self.i];
        self.i += 1;
        let mut out: Vec<u8> = vec![];
        while let Some(&c) = self.s.get(self.i) {
            self.i += 1;
            if c == q {
                return String::from_utf8(out).map_err(|_| "Malformed UTF-8".to_string());
            }
            if c == b'\\' {
                let e = match self.s.get(self.i) {
                    Some(&e) => e,
                    None => break,
                };
                self.i += 1;
                match e {
                    b'n' => out.push(b'\n'),
                    b't' => out.push(b'\t'),
                    b'r' => out.push(b'\r'),
                    b'b' => out.push(8),
                    b'f' => out.push(12),
                    b'u' => {
                        let hex = std::str::from_utf8(self.s.get(self.i..self.i + 4).unwrap_or(&[])).unwrap_or("");
                        let cp = u32::from_str_radix(hex, 16).map_err(|_| "Malformed \\u escape".to_string())?;
                        self.i += 4;
                        let mut buf = [0u8; 4];
                        out.extend_from_slice(char::from_u32(cp).unwrap_or('?').encode_utf8(&mut buf).as_bytes());
                    }
                    other => out.push(other),
                }
            } else {
                out.push(c);
            }
        }
        self.err("Unterminated string")
    }
}

// Java: Json.getValue
fn json_value(j: &Json) -> Result<Value, String> {
    match j {
        Json::Arr(items) => {
            let mut v = Vec::with_capacity(items.len());
            for x in items {
                v.push(json_value(x)?);
            }
            Ok(Value::tuple(v))
        }
        Json::Obj(fields) => {
            let mut v = Vec::with_capacity(fields.len());
            for (k, x) in fields {
                v.push((intern::intern(k), json_value(x)?));
            }
            Ok(Value::record(v))
        }
        Json::Num(n) => Ok(Value::Int(*n as i32)),
        Json::Bool(b) => Ok(Value::Bool(*b)),
        Json::Str(s) => Ok(Value::str(s)),
        Json::Null => Err("Cannot convert value: unsupported JSON value null".to_string()),
    }
}

const ND_DESERIALIZE: &str =
    "public static tlc2.value.IValue tlc2.overrides.Json.ndDeserialize(tlc2.value.impl.StringValue) throws java.io.IOException";
const DESERIALIZE: &str =
    "public static tlc2.value.IValue tlc2.overrides.Json.deserialize(tlc2.value.impl.StringValue) throws java.io.IOException";

fn json_path(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value], sig: &str) -> R<(String, Vec<u8>)> {
    let p = match arg(ev, a, 0, s0, s1)? {
        Value::Str(id) => intern::name_of(id).to_string(),
        v => return override_error(sig, &format!("class {} cannot be cast to class tlc2.value.impl.StringValue", v.to_tla())),
    };
    match std::fs::read(&p) {
        Ok(b) => Ok((p, b)),
        Err(e) => override_error(sig, &file_not_found_message(&p, &e)),
    }
}

const IO_DESERIALIZE: &str =
    "public static final tlc2.value.IValue tlc2.overrides.IOUtils.ioDeserialize(tlc2.value.impl.StringValue,tlc2.value.impl.BoolValue) throws java.io.IOException";

// Java: IOUtils.ioDeserialize: the value stored in a file (`ValueInputStream`); only the failure to open the file is reproduced
fn io_deserialize(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let p = match arg(ev, a, 0, s0, s1)? {
        Value::Str(id) => intern::name_of(id).to_string(),
        v => return override_error(IO_DESERIALIZE, &format!("class {} cannot be cast to class tlc2.value.impl.StringValue", v.to_tla())),
    };
    let _compress = arg(ev, a, 1, s0, s1)?;
    match std::fs::File::open(&p) {
        Err(e) => override_error(IO_DESERIALIZE, &file_not_found_message(&p, &e)),
        Ok(_) => not_ported("IODeserialize of an existing file"),
    }
}

// Java: Json.ndDeserialize: a tuple of the newline delimited JSON values of a file
fn json_nd_deserialize(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let (_, bytes) = json_path(ev, a, s0, s1, ND_DESERIALIZE)?;
    let text = String::from_utf8_lossy(&bytes).to_string();
    let mut values = vec![];
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let mut r = JsonReader { s: line.as_bytes(), i: 0 };
        let j = match r.value() {
            Ok(j) => j,
            Err(m) => return override_error(ND_DESERIALIZE, &format!("com.google.gson.JsonSyntaxException: {}", m)),
        };
        match json_value(&j) {
            Ok(v) => values.push(v),
            Err(m) => return override_error(ND_DESERIALIZE, &format!("java.io.IOException: {}", m)),
        }
    }
    Ok(Value::tuple(values))
}

// Java: Json.deserialize: the JSON value of a file
fn json_deserialize(ev: &Ev, a: &mut Vec<Slot>, s0: &[Value], s1: &[Value]) -> R<Value> {
    let (_, bytes) = json_path(ev, a, s0, s1, DESERIALIZE)?;
    let text = String::from_utf8_lossy(&bytes).to_string();
    let mut r = JsonReader { s: text.as_bytes(), i: 0 };
    let j = match r.value() {
        Ok(j) => j,
        Err(m) => return override_error(DESERIALIZE, &format!("com.google.gson.JsonSyntaxException: {}", m)),
    };
    match json_value(&j) {
        Ok(v) => Ok(v),
        Err(m) => override_error(DESERIALIZE, &format!("java.io.IOException: {}", m)),
    }
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
    if let Value::Fcn(f) = b {
        return Ok(f.vals.iter().all(|v| matches!(v, Value::Int(n) if *n > 0)));
    }
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

/// `B1 (+) B2` for two bags that are functions with sorted domains: one merge, the result is already sorted.
/// `None` (use the general code) when two elements cannot be compared.
fn merge_bags(f1: &Fcn, f2: &Fcn) -> R<Option<Value>> {
    let (d1, v1, d2, v2) = (&f1.dom, &f1.vals, &f2.dom, &f2.vals);
    let mut dom: Vec<Value> = Vec::with_capacity(d1.len() + d2.len());
    let mut vals: Vec<Value> = Vec::with_capacity(d1.len() + d2.len());
    let (mut i, mut j) = (0, 0);
    while i < d1.len() && j < d2.len() {
        match d1[i].cmp_val(&d2[j]) {
            Ok(std::cmp::Ordering::Less) => {
                dom.push(d1[i].clone());
                vals.push(v1[i].clone());
                i += 1;
            }
            Ok(std::cmp::Ordering::Greater) => {
                dom.push(d2[j].clone());
                vals.push(v2[j].clone());
                j += 1;
            }
            Ok(std::cmp::Ordering::Equal) => {
                let n = match (&v1[i], &v2[j]) {
                    (Value::Int(x), Value::Int(y)) => match x.checked_add(*y) {
                        Some(n) => Value::Int(n),
                        None => return fail_code(ec::TLC_MODULE_OVERFLOW, format!("Overflow when computing {}+{}", x, y)),
                    },
                    _ => return Ok(None),
                };
                dom.push(d1[i].clone());
                vals.push(n);
                i += 1;
                j += 1;
            }
            Err(_) => return Ok(None),
        }
    }
    while i < d1.len() {
        dom.push(d1[i].clone());
        vals.push(v1[i].clone());
        i += 1;
    }
    while j < d2.len() {
        dom.push(d2[j].clone());
        vals.push(v2[j].clone());
        j += 1;
    }
    Ok(Some(Value::fcn_sorted(dom, vals)))
}

/// `B1 (-) B2` for two bags that are functions with sorted domains; `None` = use the general code
fn subtract_bags(f1: &Fcn, f2: &Fcn) -> Option<Value> {
    let (d1, v1, d2, v2) = (&f1.dom, &f1.vals, &f2.dom, &f2.vals);
    let mut dom: Vec<Value> = Vec::with_capacity(d1.len());
    let mut vals: Vec<Value> = Vec::with_capacity(d1.len());
    let mut j = 0;
    for (i, d) in d1.iter().enumerate() {
        let mut n = match &v1[i] {
            Value::Int(n) => *n,
            _ => return None,
        };
        // skip the elements of B2 that are smaller than d
        while j < d2.len() {
            match d2[j].cmp_val(d) {
                Ok(std::cmp::Ordering::Less) => j += 1,
                Ok(_) => break,
                Err(_) => return None,
            }
        }
        if j < d2.len() {
            match d2[j].cmp_val(d) {
                Ok(std::cmp::Ordering::Equal) => match &v2[j] {
                    Value::Int(m) => n -= *m,
                    _ => return None,
                },
                Ok(_) => {}
                Err(_) => return None,
            }
        }
        if n > 0 {
            dom.push(d.clone());
            vals.push(Value::Int(n));
        }
    }
    Some(Value::fcn_sorted(dom, vals))
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
    if let (Value::Fcn(f1), Value::Fcn(f2)) = (&b1, &b2) {
        if let Some(r) = merge_bags(f1, f2)? {
            return Ok(r);
        }
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
    if let (Value::Fcn(f1), Value::Fcn(f2)) = (&b1, &b2) {
        if let Some(r) = subtract_bags(f1, f2) {
            return Ok(r);
        }
    }
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

/// value-level entry points of hot, pure natives with one or two ordinary arguments: called without building `Slot`s
#[derive(Clone, Copy)]
pub enum Fast {
    None,
    F1(fn(&Value) -> R<Value>),
    F2(fn(&Value, &Value) -> R<Value>),
}

pub fn lookup_fast(module: &str, name: &str) -> Fast {
    match (module, name) {
        ("Sequences", "Len") => Fast::F1(len1),
        ("Sequences", "Head") => Fast::F1(head1),
        ("Sequences", "Tail") => Fast::F1(tail1),
        ("Sequences", "Append") => Fast::F2(append2),
        ("FiniteSets", "Cardinality") => Fast::F1(cardinality1),
        _ => Fast::None,
    }
}

static RANDOM_USED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// has a random operator (`RandomElement`, `Randomization`) been bound?
pub fn random_used() -> bool {
    RANDOM_USED.load(std::sync::atomic::Ordering::Relaxed)
}

pub fn lookup(module: &str, name: &str) -> Option<NativeFn> {
    if module == "Randomization" || (module == "TLC" && name == "RandomElement") {
        RANDOM_USED.store(true, std::sync::atomic::Ordering::Relaxed);
    }
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
        ("TLCExt", "TLCGetOrDefault") => tlc_get_or_default,
        ("TLCExt", "TLCModelValue") => tlc_model_value,
        ("TLCExt", "CounterExample") => counter_example,
        ("TLCExt", "Trace") => ext_trace,
        ("TLCExt", "ToTrace") => to_trace,
        ("TLCExt", "TLCFP") => tlc_fp,
        ("TLCExt", "AssertError") => assert_error,
        ("Randomization", "RandomSubset") => random_subset,
        ("_Possible", "_Counts") => possible_counts,
        ("Functions", "FoldFunctionOnSet") => fold_function_on_set,
        ("Functions", "FoldFunction") => fold_function,
        ("Functions", "IsInjective") => is_injective,
        ("Functions", "AntiFunction") => anti_function,
        ("FiniteSetsExt", "FoldSet") => fold_set,
        ("FiniteSetsExt", "kSubset") => k_subset,
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
        ("IOUtils", "Serialize") => io_serialize,
        ("IOUtils", "IODeserialize") => io_deserialize,
        ("SequencesExt", "SetToSeq") => set_to_seq,
        ("SVG", "SVGElemToString") => svg_elem_to_string,
        ("Json", "ndJsonDeserialize") => json_nd_deserialize,
        ("Json", "JsonDeserialize") => json_deserialize,
        _ => return None,
    };
    Some(f)
}

#[cfg(test)]
mod fast_tests {
    use super::*;

    fn ints(v: &[i32]) -> Value {
        Value::tuple(v.iter().map(|&i| Value::Int(i)).collect())
    }

    #[test]
    fn sequence_natives_without_copies() {
        let s = ints(&[7, 8, 9]);
        assert_eq!(len1(&s).unwrap().to_tla(), "3");
        assert_eq!(len1(&Value::str("abc")).unwrap().to_tla(), "3");
        assert_eq!(head1(&s).unwrap().to_tla(), "7");
        assert_eq!(tail1(&s).unwrap().to_tla(), "<<8, 9>>");
        assert_eq!(append2(&s, &Value::Int(1)).unwrap().to_tla(), "<<7, 8, 9, 1>>");
        // the argument is shared, not modified
        assert_eq!(s.to_tla(), "<<7, 8, 9>>");
        assert!(head1(&ints(&[])).is_err());
        assert!(tail1(&ints(&[])).is_err());
        assert!(len1(&Value::Int(1)).is_err());
        assert_eq!(cardinality1(&Value::Interval(1, 4)).unwrap().to_tla(), "4");
        assert_eq!(cardinality1(&Value::set_from(vec![Value::Int(1), Value::Int(1)]).unwrap()).unwrap().to_tla(), "1");
        assert!(cardinality1(&Value::Int(3)).is_err());
    }

    fn bag(pairs: &[(i32, i32)]) -> Value {
        Value::fcn_from(pairs.iter().map(|&(k, n)| (Value::Int(k + 10), Value::Int(n))).collect()).unwrap()
    }

    #[test]
    fn bag_union_and_difference_by_merging_sorted_domains() {
        let (a, b) = (bag(&[(1, 2), (3, 1)]), bag(&[(1, 1), (2, 5)]));
        let (Value::Fcn(fa), Value::Fcn(fb)) = (&a, &b) else { panic!("bags are functions") };
        // (1 :> 3) @@ (2 :> 5) @@ (3 :> 1), keys shifted by 10
        assert_eq!(merge_bags(fa, fb).unwrap().unwrap().to_tla(), bag(&[(1, 3), (2, 5), (3, 1)]).to_tla());
        // elements whose count drops to 0 disappear, absent elements are ignored
        assert_eq!(subtract_bags(fa, fb).unwrap().to_tla(), bag(&[(1, 1), (3, 1)]).to_tla());
        assert_eq!(subtract_bags(fb, fa).unwrap().to_tla(), bag(&[(2, 5)]).to_tla());
        // x (-) x is the empty bag (the empty function is the empty tuple)
        assert_eq!(subtract_bags(fa, fa).unwrap().to_tla(), "<<>>");
        // elements of different kinds cannot be compared: the caller falls back to the general code
        let mixed = Value::fcn_from(vec![(Value::str("s"), Value::Int(1))]).unwrap();
        let Value::Fcn(fm) = &mixed else { panic!() };
        assert!(merge_bags(fa, fm).unwrap().is_none());
        assert!(subtract_bags(fa, fm).is_none());
    }
}
