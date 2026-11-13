//! Pollard rho, Brent's variant. It iterates `x ↦ x² + c mod m`, compares a saved iterate with a
//! stretch of later ones through batched gcds, and isolates the factor when a batch collapses.

use num_traits::{One, Zero};

use crate::arith::{gcd, mulmod, nontrivial_divisor, BigUint};

/// The number of differences `|x − y|` multiplied together before one gcd with `m`.
const BATCH: u64 = 128;

/// Pollard rho on `m` with `x ↦ x² + c`, started at 2. Returns a nontrivial divisor of `m`, or
/// `None` when the `max_steps` steps run out or the sequence cycles modulo every prime factor
/// at once (another `c` gives another sequence). `m` is odd, composite and not a perfect power.
///
/// A step is one evaluation of the polynomial on the running iterate. Redoing a collapsed batch
/// one step at a time does not count towards `max_steps`.
pub fn pollard_rho(m: &BigUint, c: u64, max_steps: u64) -> Option<BigUint> {
    // No `1 < d < m` exists below 4, and the reductions below need `m > 0`.
    if m.bits() < 3 {
        return None;
    }
    let c = BigUint::from(c) % m;
    // `x` is the saved iterate, `y` the running one, `ys` the running one at the start of the
    // current batch and `q` the product of the differences.
    let mut x = BigUint::from(2u32);
    let mut y = x.clone();
    let mut ys = x.clone();
    let mut q = BigUint::one();
    let mut diff = BigUint::zero();
    let mut r: u64 = 1;
    let mut steps: u64 = 0;
    loop {
        x.clone_from(&y);
        // Brent compares `x` with the second half of each doubling only, so `y` first moves `r`
        // steps ahead without a difference being taken.
        for _ in 0..r {
            if steps == max_steps {
                return None;
            }
            step(&mut y, &c, m);
            steps += 1;
        }
        let mut k = 0;
        while k < r {
            if steps == max_steps {
                return None;
            }
            let batch = BATCH.min(r - k).min(max_steps - steps);
            ys.clone_from(&y);
            for _ in 0..batch {
                step(&mut y, &c, m);
                abs_diff_into(&mut diff, &x, &y);
                q = mulmod(&q, &diff, m);
            }
            steps += batch;
            k += batch;
            let g = gcd(&q, m);
            if g.is_one() {
                continue;
            }
            if g != *m {
                return nontrivial_divisor(m, g);
            }
            return isolate(&x, &mut ys, batch, &c, m);
        }
        r = r.saturating_mul(2);
    }
}

/// Replaces `y` by `y² + c mod m`, for `y, c < m`.
fn step(y: &mut BigUint, c: &BigUint, m: &BigUint) {
    *y = mulmod(y, y, m);
    *y += c;
    if *y >= *m {
        *y -= m;
    }
}

/// Writes `|a − b|` into `out`, reusing its buffer.
fn abs_diff_into(out: &mut BigUint, a: &BigUint, b: &BigUint) {
    let (large, small) = if a >= b { (a, b) } else { (b, a) };
    out.clone_from(large);
    *out -= small;
}

/// Redoes a batch of `batch` steps from its starting iterate `ys`, one gcd per difference from
/// the saved iterate `x`. Returns the first gcd above 1 when it is a proper divisor, and
/// `None` when it is `m` (a cycle modulo every prime factor of `m` at the same step).
fn isolate(x: &BigUint, ys: &mut BigUint, batch: u64, c: &BigUint, m: &BigUint) -> Option<BigUint> {
    let mut diff = BigUint::zero();
    for _ in 0..batch {
        step(ys, c, m);
        abs_diff_into(&mut diff, x, ys);
        let g = gcd(&diff, m);
        if !g.is_one() {
            return nontrivial_divisor(m, g);
        }
    }
    // Unreachable, since `m` divides the product of these differences.
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith::{is_small_prime, miller_rabin};

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    /// Runs rho on `p * q` and checks that it returns one prime and leaves the other.
    fn splits(p: u64, q: u64, c: u64) {
        assert!(is_small_prime(p), "{p} is not prime");
        assert!(is_small_prime(q), "{q} is not prime");
        let (p, q) = (BigUint::from(p), BigUint::from(q));
        let m = &p * &q;
        let d = pollard_rho(&m, c, 1 << 20).unwrap_or_else(|| panic!("{p} * {q}, c = {c}"));
        assert!((&m % &d).is_zero(), "{d} does not divide {m}");
        assert!(d == p || d == q, "{d} is neither {p} nor {q}");
        assert_eq!(&m / &d, if d == p { q } else { p });
    }

    #[test]
    fn splits_products_of_two_primes_of_8_to_10_digits() {
        splits(10_000_019, 99_999_989, 1); // 8 and 8 digits
        splits(100_000_007, 999_999_937, 1); // 9 and 9 digits
        splits(1_000_000_007, 9_999_999_967, 1); // 10 and 10 digits
        splits(10_000_019, 9_999_999_967, 1); // 8 and 10 digits
        splits(2_147_483_647, 4_294_967_291, 1); // 2^31 - 1 and 2^32 - 5
    }

    #[test]
    fn c_equal_to_1_and_to_2_both_work() {
        splits(10_000_019, 99_999_989, 2);
        splits(100_000_007, 999_999_937, 2);
        // With `c = 2` the larger prime comes out first here.
        splits(1_000_000_007, 9_999_999_967, 2);
        let m = BigUint::from(10_000_079u64) * BigUint::from(12_345_701u64);
        for c in [1, 2] {
            assert_eq!(
                pollard_rho(&m, c, 1 << 20),
                Some(big("10000079")),
                "c = {c}"
            );
        }
    }

    #[test]
    fn a_prime_or_a_tiny_budget_gives_none() {
        // The sequence modulo the prime 1000003 cycles after a few thousand steps, far inside
        // the budget, so this is the degenerate-cycle exit.
        assert_eq!(pollard_rho(&big("1000003"), 1, 1 << 20), None);
        assert_eq!(pollard_rho(&big("1000003"), 2, 1 << 20), None);
        // 2^61 - 1 cannot cycle within 1024 steps, so this is the budget exit.
        assert_eq!(pollard_rho(&big("2305843009213693951"), 1, 1024), None);
        let m = BigUint::from(3u32) * big("1000000007");
        assert_eq!(pollard_rho(&m, 1, 0), None);
        assert_eq!(pollard_rho(&m, 1, 1), None);
        // Two 10-digit primes need tens of thousands of steps.
        let m = big("1000000007") * big("9999999967");
        assert_eq!(pollard_rho(&m, 1, 100), None);
        for m in [0u32, 1, 2, 3, 4, 7] {
            assert_eq!(pollard_rho(&BigUint::from(m), 1, 1 << 10), None, "{m}");
        }
    }

    #[test]
    fn a_small_factor_3_is_found_almost_instantly() {
        // `|x₀ − x₂|` is 24 for `c = 1` and 36 for `c = 2`, both divisible by 3, so the first
        // batch gcd (after two steps) is 3.
        let three = BigUint::from(3u32);
        for p in ["1000000007", "618970019642690137449562111"] {
            let p = big(p);
            assert!(miller_rabin(&p).is_ok());
            let m = &three * &p;
            for c in [1, 2] {
                assert_eq!(pollard_rho(&m, c, 4), Some(three.clone()), "{p}, c = {c}");
            }
        }
    }

    #[test]
    fn every_returned_divisor_is_nontrivial_and_divides() {
        let mut composites = 0;
        let mut split_by_c = [0; 3];
        for m in (9..2000u64).step_by(2) {
            let is_prime = is_small_prime(m);
            if !is_prime {
                composites += 1;
            }
            let big_m = BigUint::from(m);
            for (i, c) in [1, 2, 3].into_iter().enumerate() {
                if let Some(d) = pollard_rho(&big_m, c, 2000) {
                    assert!(!is_prime, "a divisor {d} of the prime {m}");
                    assert!(BigUint::one() < d && d < big_m, "{d} for {m}");
                    assert!((&big_m % &d).is_zero(), "{d} does not divide {m}");
                    split_by_c[i] += 1;
                }
            }
        }
        assert_eq!(composites, 697);
        for (i, split) in split_by_c.iter().enumerate() {
            assert!(
                *split * 10 >= composites * 9,
                "c = {}: {split}/{composites}",
                i + 1
            );
        }
    }
}
