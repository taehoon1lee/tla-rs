//! Port of `java.util.Random` (the 48-bit linear congruential generator), used by TLC's `RandomElement`
//! (`tlc2.value.RandomEnumerableValues`, `SetEnumValue.randomElement`).

const MULT: i64 = 0x5DEECE66D;
const ADD: i64 = 0xB;
const MASK: i64 = (1i64 << 48) - 1;

#[derive(Clone, Debug)]
pub struct JRandom {
    seed: i64,
}

impl JRandom {
    // Java: Random(long seed)
    pub fn new(seed: i64) -> JRandom {
        JRandom { seed: (seed ^ MULT) & MASK }
    }

    // Java: Random.setSeed(long)
    pub fn set_seed(&mut self, seed: i64) {
        self.seed = (seed ^ MULT) & MASK;
    }

    // Java: Random.next(int bits)
    fn next(&mut self, bits: u32) -> i32 {
        self.seed = self.seed.wrapping_mul(MULT).wrapping_add(ADD) & MASK;
        (self.seed >> (48 - bits)) as i32
    }

    // Java: Random.nextDouble()
    pub fn next_double(&mut self) -> f64 {
        let hi = (self.next(26) as i64) << 27;
        let lo = self.next(27) as i64;
        (hi + lo) as f64 * (1.0 / (1u64 << 53) as f64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_java_util_random() {
        // new Random(42): nextInt() sequence is -1170105035, 234785527; nextDouble() of Random(42) is 0.7275636800328681
        let mut r = JRandom::new(42);
        assert_eq!(r.next(32), -1170105035);
        assert_eq!(r.next(32), 234785527);
        let mut r = JRandom::new(42);
        assert_eq!(r.next_double(), 0.7275636800328681);
    }
}
