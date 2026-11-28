//! A compact byte encoding of state values that can cross threads.
//!
//! Not a port of a Java file.  The evaluator's values are `Rc`-based and stay inside the thread that built them; the parallel
//! search (`tlc-check/src/par.rs`) hands states from one worker thread to another as bytes.  `decode_state(encode_state(v))` has
//! the same structure as `v` (same variants, same element order), so it compares, hashes and fingerprints like `v`.
//! Lazily evaluated values (`SetPred`, `FcnLam`, `SUBSET S` of a small `S`, ...) are brought into normal form first
//! (`Value::normalize`), the same transformation a value goes through when it is stored in a state; a value that cannot be
//! brought into a concrete form makes `encode_state` return `false` (the caller then does not use the parallel search).

use crate::value::*;
use std::rc::Rc;

const T_FALSE: u8 = 0;
const T_TRUE: u8 = 1;
const T_INT: u8 = 2;
const T_STR: u8 = 3;
const T_MODEL: u8 = 4;
const T_SET: u8 = 5;
const T_TUPLE: u8 = 6;
const T_FCN: u8 = 7;
const T_INTERVAL: u8 = 8;
const T_SETU: u8 = 9;
const T_SUBSET: u8 = 10;
const T_SEQOF: u8 = 11;
const T_NAT: u8 = 12;
const T_INT_SET: u8 = 13;
const T_REAL: u8 = 14;
const T_STRING: u8 = 15;

#[inline]
fn put_u(out: &mut Vec<u8>, mut x: u64) {
    while x >= 0x80 {
        out.push((x as u8) | 0x80);
        x >>= 7;
    }
    out.push(x as u8);
}

#[inline]
fn put_i(out: &mut Vec<u8>, x: i64) {
    put_u(out, ((x << 1) ^ (x >> 63)) as u64);
}

#[inline]
fn get_u(b: &[u8], p: &mut usize) -> Option<u64> {
    let mut x = 0u64;
    let mut shift = 0;
    loop {
        let byte = *b.get(*p)?;
        *p += 1;
        x |= ((byte & 0x7F) as u64) << shift;
        if byte < 0x80 {
            return Some(x);
        }
        shift += 7;
        if shift > 63 {
            return None;
        }
    }
}

#[inline]
fn get_i(b: &[u8], p: &mut usize) -> Option<i64> {
    let u = get_u(b, p)?;
    Some(((u >> 1) as i64) ^ -((u & 1) as i64))
}

/// can `encode` write this value as it is (without normalizing it first)?
fn concrete(v: &Value) -> bool {
    matches!(
        v,
        Value::Bool(_)
            | Value::Int(_)
            | Value::Str(_)
            | Value::Model(_)
            | Value::Set(_)
            | Value::Tuple(_)
            | Value::Fcn(_)
            | Value::Interval(..)
            | Value::SetU(_)
            | Value::Subset(_)
            | Value::SeqOf(_)
            | Value::NatSet
            | Value::IntSet
            | Value::RealSet
            | Value::StringSet
    )
}

fn encode(v: &Value, out: &mut Vec<u8>) -> bool {
    match v {
        Value::Bool(b) => out.push(if *b { T_TRUE } else { T_FALSE }),
        Value::Int(i) => {
            out.push(T_INT);
            put_i(out, *i as i64);
        }
        Value::Str(id) => {
            out.push(T_STR);
            put_u(out, *id as u64);
        }
        Value::Model(id) => {
            out.push(T_MODEL);
            put_u(out, *id as u64);
        }
        Value::Set(s) | Value::Tuple(s) | Value::SetU(s) => {
            out.push(match v {
                Value::Set(_) => T_SET,
                Value::Tuple(_) => T_TUPLE,
                _ => T_SETU,
            });
            put_u(out, s.len() as u64);
            for e in s.iter() {
                if !encode(e, out) {
                    return false;
                }
            }
        }
        Value::Fcn(f) => {
            out.push(T_FCN);
            put_u(out, f.dom.len() as u64);
            for e in f.dom.iter() {
                if !encode(e, out) {
                    return false;
                }
            }
            for e in f.vals.iter() {
                if !encode(e, out) {
                    return false;
                }
            }
        }
        Value::Interval(lo, hi) => {
            out.push(T_INTERVAL);
            put_i(out, *lo as i64);
            put_i(out, *hi as i64);
        }
        Value::Subset(b) => {
            out.push(T_SUBSET);
            return encode(b, out);
        }
        Value::SeqOf(b) => {
            out.push(T_SEQOF);
            return encode(b, out);
        }
        Value::NatSet => out.push(T_NAT),
        Value::IntSet => out.push(T_INT_SET),
        Value::RealSet => out.push(T_REAL),
        Value::StringSet => out.push(T_STRING),
        _ => match v.normalize() {
            Ok(n) if concrete(&n) => return encode(&n, out),
            _ => return false,
        },
    }
    true
}

/// Append the encoding of a state; `false` (and `out` unchanged) if a value cannot be encoded.
pub fn encode_state(vals: &[Value], out: &mut Vec<u8>) -> bool {
    let mark = out.len();
    for v in vals {
        if !encode(v, out) {
            out.truncate(mark);
            return false;
        }
    }
    true
}

fn decode(b: &[u8], p: &mut usize) -> Option<Value> {
    let tag = *b.get(*p)?;
    *p += 1;
    Some(match tag {
        T_FALSE => Value::Bool(false),
        T_TRUE => Value::Bool(true),
        T_INT => Value::Int(get_i(b, p)? as i32),
        T_STR => Value::Str(get_u(b, p)? as u32),
        T_MODEL => Value::Model(get_u(b, p)? as u32),
        T_SET | T_TUPLE | T_SETU => {
            let n = get_u(b, p)? as usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(decode(b, p)?);
            }
            match tag {
                T_SET => Value::Set(Rc::new(v)),
                T_TUPLE => Value::Tuple(Rc::new(v)),
                _ => Value::SetU(Rc::new(v)),
            }
        }
        T_FCN => {
            let n = get_u(b, p)? as usize;
            let mut dom = Vec::with_capacity(n);
            for _ in 0..n {
                dom.push(decode(b, p)?);
            }
            let mut vals = Vec::with_capacity(n);
            for _ in 0..n {
                vals.push(decode(b, p)?);
            }
            Value::Fcn(Rc::new(Fcn::new(Rc::new(dom), vals)))
        }
        T_INTERVAL => {
            let lo = get_i(b, p)? as i32;
            let hi = get_i(b, p)? as i32;
            Value::Interval(lo, hi)
        }
        T_SUBSET => Value::Subset(Rc::new(decode(b, p)?)),
        T_SEQOF => Value::SeqOf(Rc::new(decode(b, p)?)),
        T_NAT => Value::NatSet,
        T_INT_SET => Value::IntSet,
        T_REAL => Value::RealSet,
        T_STRING => Value::StringSet,
        _ => return None,
    })
}

/// The state encoded in `buf` (exactly `nvars` values); `None` for malformed input.
pub fn decode_state(buf: &[u8], nvars: usize) -> Option<Vec<Value>> {
    let mut p = 0;
    let mut vals = Vec::with_capacity(nvars);
    for _ in 0..nvars {
        vals.push(decode(buf, &mut p)?);
    }
    (p == buf.len()).then_some(vals)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rt(v: Value) -> Value {
        let mut b = vec![];
        assert!(encode_state(std::slice::from_ref(&v), &mut b));
        let mut d = decode_state(&b, 1).unwrap();
        d.pop().unwrap()
    }

    #[test]
    fn scalars_and_collections_round_trip() {
        let s = Value::set_from(vec![Value::Int(3), Value::Int(-1), Value::Int(7)]).unwrap();
        let t = Value::tuple(vec![Value::Bool(true), Value::str("x"), s.clone()]);
        let r = Value::record(vec![(tla_sany::intern::intern("a"), Value::Int(1)), (tla_sany::intern::intern("b"), t.clone())]);
        for v in [Value::Int(i32::MIN), Value::Int(i32::MAX), Value::Bool(false), s, t, r, Value::Interval(2, 9), Value::NatSet] {
            let d = rt(v.clone());
            assert_eq!(v.to_tla(), d.to_tla());
            assert!(v.eq_val(&d).unwrap_or(true));
            let (mut h1, mut h2) = (Hasher::new(), Hasher::new());
            if v.hash_into(&mut h1).is_ok() {
                d.hash_into(&mut h2).unwrap();
                assert_eq!(h1.finish(), h2.finish());
            }
        }
    }

    #[test]
    fn malformed_input_is_rejected() {
        assert!(decode_state(&[T_SET, 5, T_INT], 1).is_none());
        assert!(decode_state(&[99], 1).is_none());
        assert!(decode_state(&[T_TRUE, T_TRUE], 1).is_none());
    }
}
