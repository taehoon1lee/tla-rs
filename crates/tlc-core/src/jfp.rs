//! Port of `tlc2.util.FP64` and of the `fingerPrint(long)` methods of the values (`tlc2.value.impl.*`).
//!
//! TLC's random choices in BFS mode are seeded with the fingerprint of the predecessor state
//! (`RandomEnumerableValues.TLCStateRandom`); to draw the same numbers as Java this module computes the very same
//! 64-bit fingerprints.  The model checker's own state identity does not use it.

use crate::value::Value;
use std::cell::RefCell;
use std::rc::Rc;

// Java: FP64.Polys
const POLYS: [u64; 11] = [
    0x911498AE0E66BAD6,
    0xda8a0ba66dae0181,
    0xc02f176b8f268d9f,
    0xd617bb1220fc7812,
    0xc6fd951ad34f9f74,
    0xdd1897bd991704d4,
    0xf5394c541cbfd343,
    0xb1dded37b5c7b8f7,
    0xa3cd71299c8b3bfd,
    0x845b8031ef886f35,
    0x91f5a5fa9c5515a5,
];

// Java: ValueConstants
const MODELVALUE: u8 = 21;
const BOOLVALUE: u8 = 0;
const INTVALUE: u8 = 1;
const STRINGVALUE: u8 = 3;
const SETENUMVALUE: u8 = 5;
const FCNRCDVALUE: u8 = 9;

/// Java: `FP64` initialized with the irreducible polynomial number `index` (`-fp`)
pub struct Fp64 {
    irred: u64,
    table: [u64; 256],
}

impl Fp64 {
    // Java: FP64.Init(int)
    pub fn new(index: usize) -> Fp64 {
        let irred = POLYS[index % POLYS.len()];
        let mut power = [0u64; 72];
        let mut t: u64 = 0x8000000000000000;
        for p in power.iter_mut() {
            *p = t;
            let mask = if t & 1 != 0 { irred } else { 0 };
            t = (t >> 1) ^ mask;
        }
        let mut table = [0u64; 256];
        for (j, slot) in table.iter_mut().enumerate() {
            let mut v = 0u64;
            for k in 0..8 {
                if j & (1 << k) != 0 {
                    v ^= power[127 - 56 - k];
                }
            }
            *slot = v;
        }
        Fp64 { irred, table }
    }

    /// Java: FP64.New()
    pub fn start(&self) -> u64 {
        self.irred
    }

    fn byte(&self, fp: u64, b: u8) -> u64 {
        (fp >> 8) ^ self.table[((b as u64 ^ fp) & 0xFF) as usize]
    }

    fn int(&self, mut fp: u64, x: i32) -> u64 {
        let mut x = x as u32;
        for _ in 0..4 {
            fp = self.byte(fp, (x & 0xFF) as u8);
            x >>= 8;
        }
        fp
    }

    /// the characters of a string, one byte each (the low byte of the UTF-16 unit)
    fn chars(&self, mut fp: u64, s: &str) -> u64 {
        for c in s.encode_utf16() {
            fp = self.byte(fp, (c & 0xFF) as u8);
        }
        fp
    }

    /// Java: `Value.fingerPrint(long)`; `None` for a value this port does not know (a model value, ...)
    pub fn value(&self, fp: u64, v: &Value) -> Option<u64> {
        match v {
            Value::Bool(b) => Some(self.byte(self.byte(fp, BOOLVALUE), if *b { b't' } else { b'f' })),
            Value::Int(i) => Some(self.int(self.byte(fp, INTVALUE), *i)),
            Value::Str(id) => {
                let s = tla_sany::intern::name_of(*id);
                let fp = self.byte(fp, STRINGVALUE);
                let fp = self.int(fp, s.encode_utf16().count() as i32);
                Some(self.chars(fp, &s))
            }
            Value::Tuple(t) => {
                let mut fp = self.int(self.byte(fp, FCNRCDVALUE), t.len() as i32);
                for (i, e) in t.iter().enumerate() {
                    fp = self.int(self.byte(fp, INTVALUE), i as i32 + 1);
                    fp = self.value(fp, e)?;
                }
                Some(fp)
            }
            Value::Fcn(f) => {
                let mut fp = self.int(self.byte(fp, FCNRCDVALUE), f.dom.len() as i32);
                for (d, x) in f.dom.iter().zip(f.vals.iter()) {
                    fp = self.value(fp, d)?;
                    fp = self.value(fp, x)?;
                }
                Some(fp)
            }
            Value::Model(id) => Some(self.int(self.byte(fp, MODELVALUE), model_tok(*id)?)),
            Value::Set(s) => self.set(fp, s),
            Value::Interval(lo, hi) => {
                let n = if hi < lo { 0 } else { (*hi as i64 - *lo as i64 + 1) as i32 };
                let mut fp = self.int(self.byte(fp, SETENUMVALUE), n);
                for i in 0..n as i64 {
                    fp = self.int(self.byte(fp, INTVALUE), (*lo as i64 + i) as i32);
                }
                Some(fp)
            }
            other => {
                let e = other.enumerate().ok()?;
                self.set(fp, &e)
            }
        }
    }

    fn set(&self, fp: u64, elems: &Rc<Vec<Value>>) -> Option<u64> {
        let mut fp = self.int(self.byte(fp, SETENUMVALUE), elems.len() as i32);
        for e in elems.iter() {
            fp = self.value(fp, e)?;
        }
        Some(fp)
    }

    /// like `state`, `None` when a value is not known to this port
    pub fn state_opt(&self, vals: &[Value]) -> Option<u64> {
        let mut fp = self.start();
        for v in vals {
            fp = self.value(fp, v)?;
        }
        Some(fp)
    }

    /// Java: `TLCStateMut.fingerPrint()` (without symmetry and VIEW): the values of the variables in order
    pub fn state(&self, vals: &[Value]) -> u64 {
        let mut fp = self.start();
        for v in vals {
            fp = self.value(fp, v).unwrap_or(fp);
        }
        fp
    }
}

thread_local! {
    static CACHE: RefCell<Option<(usize, Rc<Fp64>)>> = const { RefCell::new(None) };
    /// Java: `UniqueString.tok` of the model values of the configuration file (the first strings the JVM interns, in the order the
    /// file mentions them: 1, 2, ...), by intern id
    static MODEL_TOKS: RefCell<std::collections::HashMap<u32, i32>> = RefCell::new(std::collections::HashMap::new());
}

/// register the tokens of the strings of the configuration file (`order`: see `ModelConfig::value_order`)
pub fn set_model_toks(order: &[String]) {
    MODEL_TOKS.with(|m| {
        let mut m = m.borrow_mut();
        m.clear();
        for (i, s) in order.iter().enumerate() {
            m.insert(tla_sany::intern::intern(s), i as i32 + 1);
        }
    });
}

fn model_tok(id: u32) -> Option<i32> {
    MODEL_TOKS.with(|m| m.borrow().get(&id).copied())
}

/// the `FP64` of the polynomial `index` (built once)
pub fn fp64(index: usize) -> Rc<Fp64> {
    CACHE.with(|c| {
        let mut c = c.borrow_mut();
        if let Some((i, f)) = &*c {
            if *i == index {
                return f.clone();
            }
        }
        let f = Rc::new(Fp64::new(index));
        *c = Some((index, f.clone()));
        f
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extends_like_java() {
        // FP64.Init(0); FP64.New() is the polynomial itself; extending by the byte 0 and then 'a' is table driven
        let f = Fp64::new(0);
        assert_eq!(f.start(), 0x911498AE0E66BAD6);
        // the table entry for 0 is 0: extending by a byte equal to the low byte of fp keeps the shifted fp
        let fp = f.start();
        let b = (fp & 0xFF) as u8;
        assert_eq!(f.byte(fp, b), fp >> 8);
    }
}
