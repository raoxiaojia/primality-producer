//! Pollard p−1 (stage 1 and a simple stage 2). A prime factor `p` of `m` is found when the order
//! of 3 modulo `p` is `b1`-smooth, or `b1`-smooth times one prime in `(b1, b2]`.

use num_traits::{One, Zero};

use crate::arith::{gcd, mulmod, nontrivial_divisor, powmod, small_primes, BigUint};

/// The number of primes walked between two gcd computations, in both stages.
const GCD_INTERVAL: usize = 1000;

/// Pollard p−1 with base 3 and the bounds `b1`, `b2`. Returns a nontrivial divisor of `m` or
/// `None`. The primes walked stop at `2^32 - 2` whatever the bounds.
pub fn pollard_pm1(m: &BigUint, b1: u64, b2: u64) -> Option<BigUint> {
    if m.bits() < 2 {
        // `m < 2` has no nontrivial divisor, and a reduction modulo 0 would panic.
        return None;
    }
    // `small_primes` lists the primes below its bound.
    let top = u32::try_from(b1.max(b2))
        .unwrap_or(u32::MAX)
        .min(u32::MAX - 1);
    let primes = small_primes(top + 1);
    let split = primes.partition_point(|&p| u64::from(p) <= b1);
    let (stage1_primes, rest) = primes.split_at(split);
    let stage2_primes = &rest[..rest.partition_point(|&p| u64::from(p) <= b2)];
    let x = match stage1(m, b1, stage1_primes) {
        Stage1::Divisor(d) => return nontrivial_divisor(m, d),
        Stage1::Exhausted => return None,
        Stage1::Continue(x) => x,
    };
    stage2(m, &x, stage2_primes)
}

/// `x − 1` modulo `m`, for `x < m`. The `x` here are powers of 3, so `x = 0` occurs when `m` is
/// a power of 3.
fn minus_one(x: &BigUint, m: &BigUint) -> BigUint {
    if x.is_zero() {
        m - 1u32
    } else {
        x - 1u32
    }
}

/// The largest power of the prime `p` not exceeding `bound`, for `p ≤ bound`.
fn largest_power_within(p: u32, bound: u64) -> u64 {
    let p = u64::from(p);
    let mut power = p;
    while let Some(next) = power.checked_mul(p) {
        if next > bound {
            break;
        }
        power = next;
    }
    power
}

/// What stage 1 ends with.
enum Stage1 {
    /// A divisor of `m` (the caller checks it).
    Divisor(BigUint),
    /// `3^E ≡ 1 (mod m)` for the stage 1 exponent `E`, and no prime of the last block separates
    /// the factors of `m`. Stage 2 would then accumulate only zeros.
    Exhausted,
    /// `3^E mod m`, with `gcd(3^E − 1, m) = 1`, for stage 2.
    Continue(BigUint),
}

/// Stage 1 over `primes`, the primes `≤ b1` ascending.
fn stage1(m: &BigUint, b1: u64, primes: &[u32]) -> Stage1 {
    let mut x = BigUint::from(3u32) % m;
    // The value of `x` after the blocks before the current one.
    let mut checkpoint = x.clone();
    for block in primes.chunks(GCD_INTERVAL) {
        // Multiply the prime powers of the block into one exponent while it fits a `u64`, so
        // that `powmod` runs once per 64 bits of exponent instead of once per prime.
        let mut exponent = 1u64;
        for &p in block {
            let power = largest_power_within(p, b1);
            match exponent.checked_mul(power) {
                Some(product) => exponent = product,
                None => {
                    x = powmod(&x, &BigUint::from(exponent), m);
                    exponent = power;
                }
            }
        }
        if exponent > 1 {
            x = powmod(&x, &BigUint::from(exponent), m);
        }
        let g = gcd(&minus_one(&x, m), m);
        if g.is_one() {
            checkpoint = x.clone();
            continue;
        }
        if g != *m {
            return Stage1::Divisor(g);
        }
        // Every prime factor of `m` was reached within this block. Redo it one prime at a time
        // and stop at the first prime after which some factor is reached and some is not.
        x = checkpoint;
        for &p in block {
            x = powmod(&x, &BigUint::from(largest_power_within(p, b1)), m);
            let g = gcd(&minus_one(&x, m), m);
            if g == *m {
                return Stage1::Exhausted;
            }
            if !g.is_one() {
                return Stage1::Divisor(g);
            }
        }
        // Unreachable, since redoing the whole block reproduces the gcd `m`.
        return Stage1::Exhausted;
    }
    Stage1::Continue(x)
}

/// The state of the stage 2 walk.
#[derive(Clone)]
struct Walk {
    /// The last prime walked, or 0 before the first one.
    prev: u32,
    /// `x^prev mod m`.
    y: BigUint,
    /// `∏ (x^q − 1) mod m` over the primes walked so far.
    acc: BigUint,
}

/// The fixed data of stage 2. `gap_powers[k] = x^(2k) mod m` is extended on demand to the
/// largest prime gap met.
struct Stage2<'a> {
    m: &'a BigUint,
    x: &'a BigUint,
    x2: BigUint,
    gap_powers: Vec<BigUint>,
}

impl Stage2<'_> {
    /// Moves `walk` to the prime `q`, the next after `walk.prev`, and multiplies `x^q − 1` into
    /// the accumulator.
    fn advance(&mut self, walk: &mut Walk, q: u32) {
        let gap = q - walk.prev;
        if walk.prev == 0 || !gap.is_multiple_of(2) {
            // The first prime, or the odd gap from 2 to 3 when `b1 < 2`.
            walk.y = powmod(self.x, &BigUint::from(q), self.m);
        } else {
            let k = (gap / 2) as usize;
            while self.gap_powers.len() <= k {
                let next = mulmod(
                    &self.gap_powers[self.gap_powers.len() - 1],
                    &self.x2,
                    self.m,
                );
                self.gap_powers.push(next);
            }
            walk.y = mulmod(&walk.y, &self.gap_powers[k], self.m);
        }
        walk.acc = mulmod(&walk.acc, &minus_one(&walk.y, self.m), self.m);
        walk.prev = q;
    }
}

/// Stage 2 over `primes`, the primes in `(b1, b2]` ascending, from the stage 1 value `x`.
fn stage2(m: &BigUint, x: &BigUint, primes: &[u32]) -> Option<BigUint> {
    let mut stage = Stage2 {
        m,
        x,
        x2: mulmod(x, x, m),
        gap_powers: vec![BigUint::one()],
    };
    let mut walk = Walk {
        prev: 0,
        y: BigUint::one(),
        acc: BigUint::one(),
    };
    // The walk after the blocks before the current one.
    let mut checkpoint = walk.clone();
    for block in primes.chunks(GCD_INTERVAL) {
        for &q in block {
            stage.advance(&mut walk, q);
        }
        let g = gcd(&walk.acc, m);
        if g.is_one() {
            checkpoint = walk.clone();
            continue;
        }
        if g != *m {
            return nontrivial_divisor(m, g);
        }
        // Every prime factor of `m` was reached within this block. Redo it one prime at a time.
        walk = checkpoint;
        for &q in block {
            stage.advance(&mut walk, q);
            let g = gcd(&walk.acc, m);
            if g == *m {
                return None;
            }
            if !g.is_one() {
                return nontrivial_divisor(m, g);
            }
        }
        // Unreachable, since redoing the whole block reproduces the gcd `m`.
        return None;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    /// Checks `1 < d < m` and `d | m`.
    fn assert_nontrivial_divisor(m: &BigUint, d: &BigUint) {
        assert!(*d > BigUint::one(), "{d} is not above 1");
        assert!(d < m, "{d} is not below {m}");
        assert!((m % d).is_zero(), "{d} does not divide {m}");
    }

    /// `2 · 3 · 5 · 7 · 11 · 13 · 17 · 19 · 23 · 29 · 31 + 1`, a 12-digit prime whose `p − 1` is
    /// 1000-smooth. The order of 3 modulo it has 31 as its largest prime factor.
    const P_SMOOTH: &str = "200560490131";

    /// `10^12 + 39`, a prime with `q − 1 = 2 · 3 · 13 · 17 · 29 · 26005097`, where the last
    /// factor divides the order of 3, so no bound in these tests reaches it.
    const Q_ROUGH: &str = "1000000000039";

    #[test]
    fn stage_1_splits_off_a_prime_with_a_smooth_p_minus_1() {
        let p = big(P_SMOOTH);
        let m = &p * big(Q_ROUGH);
        // 168 primes below 1000: the only gcd is the one at the end of stage 1.
        let d = pollard_pm1(&m, 1000, 1000).expect("stage 1 finds p");
        assert_nontrivial_divisor(&m, &d);
        assert_eq!(d, p);
        // 2262 primes below 20000: the gcd after the first 1000 primes already finds p.
        assert_eq!(pollard_pm1(&m, 20_000, 20_000), Some(p));
    }

    #[test]
    fn stage_2_finds_a_prime_whose_order_has_one_factor_beyond_b1() {
        // 2 · 3 · 5 · 7 · 11 · 13 · 17 · 19 · 50101 + 1, a prime. 50101 divides the order of 3.
        let p = big("485964168691");
        let m = &p * big(Q_ROUGH);
        let d = pollard_pm1(&m, 1000, 100_000).expect("stage 2 finds p");
        assert_nontrivial_divisor(&m, &d);
        assert_eq!(d, p);
        assert_eq!(pollard_pm1(&m, 1000, 1000), None);
        assert_eq!(pollard_pm1(&m, 1000, 50_000), None);
    }

    #[test]
    fn backtracking_separates_two_smooth_primes_reached_in_one_block() {
        // 2 · 3 · 5 · 7 · 11 · 13 · 17 · 19 · 23 · 29 · 37 + 1, a prime. The order of 3 modulo it
        // has 29 as its largest prime factor, so the redo reaches it one prime before P_SMOOTH.
        let p = big("239378649511");
        let m = &p * big(P_SMOOTH);
        let d = pollard_pm1(&m, 1000, 1000).expect("the redo separates the factors");
        assert_nontrivial_divisor(&m, &d);
        assert_eq!(d, p);
    }

    #[test]
    fn a_prime_m_gives_none() {
        // 2^61 - 1, whose p - 1 is 2 · 3^2 · 5^2 · 7 · 11 · 13 · 31 · 41 · 61 · 151 · 331 · 1321.
        let m61 = big("2305843009213693951");
        // 1321 > b1: the stage 1 gcd is 1.
        assert_eq!(pollard_pm1(&m61, 1000, 1000), None);
        // 1321 ≤ b1: the stage 1 gcd is m, and the redo one prime at a time ends in m too.
        assert_eq!(pollard_pm1(&m61, 2000, 2000), None);
        // 1321 ∈ (b1, b2]: the stage 2 gcd is m, with the same redo.
        assert_eq!(pollard_pm1(&m61, 1000, 2000), None);
        assert_eq!(pollard_pm1(&big("1000000000039"), 1000, 10_000), None);
    }
}
