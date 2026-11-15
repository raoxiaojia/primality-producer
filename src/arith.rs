//! Number theory on `BigUint`, and serde helpers that write a `BigUint` as a decimal string.

use std::ops::RangeInclusive;
use std::sync::OnceLock;

pub use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};

/// Deterministic PRNG (splitmix64).
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// All primes `< bound`, ascending.
pub fn small_primes(bound: u32) -> Vec<u32> {
    if bound <= 2 {
        return Vec::new(); // this also ends the recursion through the base primes of `primes_in`
    }
    primes_in(2..=u64::from(bound) - 1)
        .map(|p| p as u32)
        .collect()
}

/// The primes in `range`, ascending. The sieve works on `2^16` numbers at a time, so it holds one
/// segment and the primes up to the square root of the range's end.
pub fn primes_in(range: RangeInclusive<u64>) -> impl Iterator<Item = u64> {
    const SEGMENT: u64 = 1 << 16;
    let (lo, hi) = range.into_inner();
    let base = small_primes(u32::try_from(hi.isqrt() + 1).unwrap_or(u32::MAX));
    (lo.max(2)..=hi)
        .step_by(SEGMENT as usize)
        .flat_map(move |start| {
            let end = hi.min(start.saturating_add(SEGMENT - 1));
            let mut composite = vec![false; (end - start + 1) as usize];
            for &p in &base {
                let p = u64::from(p);
                if p * p > end {
                    break;
                }
                let mut multiple = (p * p).max(start.div_ceil(p) * p);
                while multiple <= end {
                    composite[(multiple - start) as usize] = true;
                    multiple += p;
                }
            }
            (start..=end)
                .zip(composite)
                .filter_map(|(n, composite)| (!composite).then_some(n))
        })
}

/// The primes below `2^16`, the default trial-division bound.
fn primes_below_2_16() -> &'static [u32] {
    static PRIMES: OnceLock<Vec<u32>> = OnceLock::new();
    PRIMES.get_or_init(|| small_primes(1 << 16))
}

/// Whether `x` is prime, by trial division (meant for small `x`).
pub fn is_small_prime(x: u64) -> bool {
    if x < 4 {
        return x >= 2;
    }
    if x.is_multiple_of(2) || x.is_multiple_of(3) {
        return false;
    }
    let mut c = 5u64;
    while u128::from(c) * u128::from(c) <= u128::from(x) {
        if x.is_multiple_of(c) || x.is_multiple_of(c + 2) {
            return false;
        }
        c += 6;
    }
    true
}

pub fn mulmod(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    (a * b) % m
}

pub fn powmod(b: &BigUint, e: &BigUint, m: &BigUint) -> BigUint {
    b.modpow(e, m)
}

/// `a^((q - 1) / r) mod q` for every `r` in `factors`, in their order, and `a^(q - 1) mod q`.
/// `q ≥ 1`, and no factor is 0.
///
/// When the product `R` of the factors divides `q - 1 = C · R`, the powers `x^(R / r)` are taken
/// from `x = a^C` by a product tree. For `k` factors that costs about
/// `bits(C) + (1 + log2 k) · bits(R)` squarings instead of `(k + 1) · bits(q - 1)`. Otherwise
/// every power is computed on its own.
pub fn lucas_powers(a: &BigUint, q: &BigUint, factors: &[BigUint]) -> (Vec<BigUint>, BigUint) {
    let e = q - 1u32;
    let radical = product(factors);
    if factors.is_empty() || !(&e % &radical).is_zero() {
        let powers = factors.iter().map(|r| powmod(a, &(&e / r), q)).collect();
        return (powers, powmod(a, &e, q));
    }
    let x = powmod(a, &(&e / &radical), q);
    let mut powers = vec![BigUint::zero(); factors.len()];
    split_powers(&x, factors, q, &mut powers);
    let full = powmod(&powers[0], &factors[0], q);
    (powers, full)
}

/// Fills `powers[i]` with `y^(P / factors[i]) mod q`, where `P` is the product of `factors`.
fn split_powers(y: &BigUint, factors: &[BigUint], q: &BigUint, powers: &mut [BigUint]) {
    match factors {
        [] => {}
        [_] => powers[0] = y.clone(),
        _ => {
            let mid = factors.len() / 2;
            let (left, right) = factors.split_at(mid);
            let (left_powers, right_powers) = powers.split_at_mut(mid);
            split_powers(&powmod(y, &product(right), q), left, q, left_powers);
            split_powers(&powmod(y, &product(left), q), right, q, right_powers);
        }
    }
}

/// The product of `values` (1 for none).
fn product(values: &[BigUint]) -> BigUint {
    values.iter().fold(BigUint::one(), |acc, v| acc * v)
}

pub fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
    a.gcd(b)
}

/// `Some(d)` when `1 < d < m` and `d` divides `m`, else `None`.
pub fn nontrivial_divisor(m: &BigUint, d: BigUint) -> Option<BigUint> {
    (BigUint::one() < d && d < *m && (m % &d).is_zero()).then_some(d)
}

/// The Jacobi symbol `(a | n)` for an odd `n` (0 when `gcd(a, n) > 1`, else `±1`).
///
/// Each factor 2 removed from `a` flips the sign when `n ≡ ±3 (mod 8)`. Swapping `a` and `n` by
/// quadratic reciprocity flips it when both are `3 (mod 4)`.
pub fn jacobi(a: &BigUint, n: &BigUint) -> i8 {
    assert!(n.is_odd(), "jacobi needs an odd modulus, found {n}");
    let mut a = a % n;
    let mut n = n.clone();
    let mut result = 1i8;
    while !a.is_zero() {
        let twos = a.trailing_zeros().unwrap_or(0);
        a >>= twos;
        if twos % 2 == 1 && matches!(low_bits(&n) & 7, 3 | 5) {
            result = -result;
        }
        if low_bits(&a) & 3 == 3 && low_bits(&n) & 3 == 3 {
            result = -result;
        }
        std::mem::swap(&mut a, &mut n);
        a %= &n;
    }
    if n.is_one() {
        result
    } else {
        0
    }
}

/// The lowest 64 bits of `x`.
fn low_bits(x: &BigUint) -> u64 {
    x.iter_u64_digits().next().unwrap_or(0)
}

pub fn to_u64(x: &BigUint) -> Option<u64> {
    x.to_u64()
}

/// The number of decimal digits of `x` (`digits(0) = 1`).
pub fn digits(x: &BigUint) -> usize {
    x.to_str_radix(10).len()
}

/// Miller–Rabin with these bases is deterministic for every
/// `n < 3 317 044 064 679 887 385 961 981 ≈ 3.3·10^24` (Sorenson and Webster, "Strong
/// pseudoprimes to twelve prime bases", Math. Comp. 86 (2017), 985–1003).
const MR_PRIME_BASES: [u64; 13] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41];

const MR_RANDOM_BASE_COUNT: usize = 20;

fn mr_deterministic_bound() -> BigUint {
    BigUint::parse_bytes(b"3317044064679887385961981", 10).expect("a decimal literal")
}

/// Whether `a` passes the strong probable-prime test for the odd `n > 3`, given
/// `n - 1 = d · 2^s` with `d` odd. `a` is in `1..n`.
fn strong_probable_prime(
    n: &BigUint,
    n_minus_1: &BigUint,
    d: &BigUint,
    s: u64,
    a: &BigUint,
) -> bool {
    let mut x = a.modpow(d, n);
    if x.is_one() || x == *n_minus_1 {
        return true;
    }
    for _ in 1..s {
        x = (&x * &x) % n;
        if x == *n_minus_1 {
            return true;
        }
        if x.is_one() {
            return false;
        }
    }
    false
}

/// Miller–Rabin. `Ok(())` means probable prime. `Err(base)` names a base that proves `n`
/// composite (`Err(0)` for `n < 2`, `Err(2)` for an even `n > 2`). Above the bound where
/// `MR_PRIME_BASES` are deterministic, `MR_RANDOM_BASE_COUNT` more bases come from a PRNG seeded
/// with the low 64 bits of `n`, so the result is the same on every run.
pub fn miller_rabin(n: &BigUint) -> Result<(), u64> {
    match to_u64(n) {
        Some(0 | 1) => return Err(0),
        Some(2 | 3) => return Ok(()),
        _ => {}
    }
    if n.is_even() {
        return Err(2);
    }
    let n_minus_1 = n - 1u32;
    let s = n_minus_1.trailing_zeros().unwrap_or(0);
    let d = &n_minus_1 >> s;
    for &a in &MR_PRIME_BASES {
        if (n % a).is_zero() {
            return if to_u64(n) == Some(a) { Ok(()) } else { Err(a) };
        }
        // For `n < 41` some bases exceed `n`; their residues are still in `1..n`.
        let base = BigUint::from(a) % n;
        if !strong_probable_prime(n, &n_minus_1, &d, s, &base) {
            return Err(a);
        }
    }
    if *n < mr_deterministic_bound() {
        return Ok(());
    }
    let mut rng = Rng(low_bits(n));
    for _ in 0..MR_RANDOM_BASE_COUNT {
        // A base in `[2, 2^64 - 2]`, inside `[2, n - 2]` since `n > 2^64` here. A base of the
        // size of `n` could not be reported in the result's `u64`.
        let a = 2 + rng.next_u64() % (u64::MAX - 2);
        // `gcd(a, n) = gcd(a, n mod a)`, and `n mod a < a` fits a `u64`.
        let remainder = to_u64(&(n % a)).unwrap_or(0);
        if a.gcd(&remainder) > 1 {
            return Err(a);
        }
        if !strong_probable_prime(n, &n_minus_1, &d, s, &BigUint::from(a)) {
            return Err(a);
        }
    }
    Ok(())
}

/// Divides out all primes `< bound`; returns `(prime, exponent)` pairs ascending and the cofactor.
/// `n = 0` gives no pairs and the cofactor 0.
pub fn trial_division(n: &BigUint, bound: u32) -> (Vec<(u64, u32)>, BigUint) {
    let mut factors = Vec::new();
    let mut rest = n.clone();
    if rest.is_zero() {
        return (factors, rest);
    }
    let sieved;
    let primes = if bound <= 1 << 16 {
        primes_below_2_16()
    } else {
        sieved = small_primes(bound);
        &sieved
    };
    for &p in primes.iter().take_while(|&&p| p < bound) {
        // `rest` has no prime factor below `p`, so once `p² > rest` it is 1 or a prime.
        if let Some(r) = to_u64(&rest) {
            if u64::from(p) * u64::from(p) > r {
                break;
            }
        }
        let mut exponent = 0;
        while (&rest % p).is_zero() {
            rest /= p;
            exponent += 1;
        }
        if exponent > 0 {
            factors.push((u64::from(p), exponent));
        }
    }
    // A prime left over below `bound` belongs to the pairs.
    if let Some(r) = to_u64(&rest) {
        if r > 1 && r < u64::from(bound) {
            factors.push((r, 1));
            rest = BigUint::one();
        }
    }
    (factors, rest)
}

/// `Some((base, k))` with `k ≥ 2` prime and `base^k == n`, else `None`.
pub fn perfect_power(n: &BigUint) -> Option<(BigUint, u32)> {
    if n.bits() < 3 {
        return None; // n < 4
    }
    // `base ≥ 2` needs `2^k ≤ n`, so no exponent beyond `bits(n)` can work.
    let max_k = u32::try_from(n.bits()).unwrap_or(u32::MAX - 1);
    for k in small_primes(max_k + 1) {
        let root = n.nth_root(k);
        if root.bits() >= 2 && root.pow(k) == *n {
            return Some((root, k));
        }
    }
    None
}

/// Parses a nonempty string of ASCII digits as a `BigUint`. Anything else (the empty string, a
/// sign, an underscore, whitespace) gives `None`.
pub(crate) fn parse_decimal(s: &str) -> Option<BigUint> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    BigUint::parse_bytes(s.as_bytes(), 10)
}

/// Serde helpers writing a `BigUint` as a decimal string, for
/// `#[serde(with = "crate::arith::big_str")]`.
pub mod big_str {
    use super::{parse_decimal, BigUint};
    use serde::de::{Deserialize, Deserializer, Error as _};
    use serde::ser::Serializer;

    pub fn serialize<S: Serializer>(value: &BigUint, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&value.to_str_radix(10))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<BigUint, D::Error> {
        let s = String::deserialize(deserializer)?;
        parse_decimal(&s)
            .ok_or_else(|| D::Error::custom(format!("expected a decimal string, found {s:?}")))
    }
}

/// Serde helpers writing a `Vec<BigUint>` as an array of decimal strings, for
/// `#[serde(with = "crate::arith::big_str_vec")]`.
pub mod big_str_vec {
    use super::{parse_decimal, BigUint};
    use serde::de::{Deserialize, Deserializer, Error as _};
    use serde::ser::{SerializeSeq, Serializer};

    pub fn serialize<S: Serializer>(values: &[BigUint], serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(values.len()))?;
        for value in values {
            seq.serialize_element(&value.to_str_radix(10))?;
        }
        seq.end()
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<BigUint>, D::Error> {
        let strings = Vec::<String>::deserialize(deserializer)?;
        strings
            .iter()
            .map(|s| {
                parse_decimal(s).ok_or_else(|| {
                    D::Error::custom(format!("expected a decimal string, found {s:?}"))
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};

    use super::*;

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    /// Primality by the definition, for the brute-force comparisons.
    fn is_prime_naive(x: u64) -> bool {
        x >= 2
            && (2..x)
                .take_while(|d| d * d <= x)
                .all(|d| !x.is_multiple_of(d))
    }

    /// Whether `a` proves the odd `n > 3` composite: a common factor, or the strong test fails.
    fn is_witness(n: &BigUint, a: u64) -> bool {
        let a = BigUint::from(a);
        if !gcd(&a, n).is_one() {
            return true;
        }
        let n_minus_1 = n - 1u32;
        let s = n_minus_1.trailing_zeros().unwrap();
        let d = &n_minus_1 >> s;
        let mut x = powmod(&a, &d, n);
        if x.is_one() || x == n_minus_1 {
            return false;
        }
        for _ in 1..s {
            x = mulmod(&x, &x, n);
            if x == n_minus_1 {
                return false;
            }
        }
        true
    }

    #[test]
    fn primes_in_covers_its_range_across_segments() {
        let primes = |range: RangeInclusive<u64>| primes_in(range).collect::<Vec<_>>();
        assert_eq!(primes(0..=30), [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]);
        // ECM's stage 2 range `(b1, b2]` with `b2 = b1`.
        let b1 = 2000;
        assert!(primes(b1 + 1..=b1).is_empty());
        assert_eq!(primes(2..=2), [2]);
        // Four segments of 2^16, the range starting and ending inside one, with
        // π(200000) − π(999) = 17816 primes.
        let inside = primes(1000..=200_000);
        assert_eq!(
            (inside.len(), inside[0], inside[inside.len() - 1]),
            (17_816, 1009, 199_999)
        );
        assert!(inside.iter().all(|&p| is_prime_naive(p)));
        // A range above `u32`.
        assert_eq!(primes(1 << 32..=(1 << 32) + 20), [4_294_967_311]);
    }

    /// The distinct prime factors of `m`, ascending, by trial division (`m < 2^32`).
    fn distinct_prime_factors(m: u64) -> Vec<BigUint> {
        let (pairs, rest) = trial_division(&BigUint::from(m), 65_536);
        assert!(rest.is_one(), "{m} has a factor above 2^16");
        pairs.iter().map(|&(p, _)| BigUint::from(p)).collect()
    }

    /// `lucas_powers` against one `powmod` per power.
    fn check_lucas_powers(a: &BigUint, q: &BigUint, factors: &[BigUint]) {
        let e = q - 1u32;
        let expected: Vec<BigUint> = factors.iter().map(|r| powmod(a, &(&e / r), q)).collect();
        let (powers, full) = lucas_powers(a, q, factors);
        assert_eq!(powers, expected, "a = {a}, q = {q}, factors {factors:?}");
        assert_eq!(full, powmod(a, &e, q), "a = {a}, q = {q}");
    }

    #[test]
    fn lucas_powers_agrees_with_separate_exponentiations() {
        // Primes with the distinct prime factors of `q - 1`, for every base up to 30, among them
        // the non-primitive roots (4 for every odd prime, 2 for 1009).
        for q in [
            3u64,
            5,
            7,
            13,
            17,
            65_521,
            65_537,
            104_729,
            1009,
            1289,
            2_147_483_647,
        ] {
            let factors = distinct_prime_factors(q - 1);
            let q = BigUint::from(q);
            for a in 0..30u64 {
                check_lucas_powers(&BigUint::from(a), &q, &factors);
            }
        }
        // A single factor (65536 = 2^16), and a cofactor `C > 1` beside the radical
        // (1008 = 2^4 · 3^2 · 7, so `C = 24`).
        let q = BigUint::from(65_537u32);
        let (powers, full) = lucas_powers(&BigUint::from(3u32), &q, &[BigUint::from(2u32)]);
        assert_eq!(powers, [BigUint::from(65_536u32)]); // 3^32768 ≡ -1
        assert!(full.is_one());
        let (powers, full) = lucas_powers(&BigUint::from(4u32), &q, &[BigUint::from(2u32)]);
        assert!(powers[0].is_one() && full.is_one()); // 4 is a square
        let q = BigUint::from(1009u32);
        let factors = [2u32, 3, 7].map(BigUint::from);
        let (powers, full) = lucas_powers(&BigUint::from(11u32), &q, &factors);
        assert!(powers.iter().all(|p| !p.is_one()) && full.is_one()); // 11 is a root
                                                                      // 2 is a square modulo 1009.
        let (powers, _) = lucas_powers(&BigUint::from(2u32), &q, &factors);
        assert!(powers[0].is_one());
        // With a composite `q` the powers are plain modular arithmetic.
        let q = BigUint::from(1001u32); // 1000 = 2^3 · 5^3
        let factors = [2u32, 5].map(BigUint::from);
        for a in 0..30u64 {
            check_lucas_powers(&BigUint::from(a), &q, &factors);
        }
        // No factor at all, and a product of the factors that does not divide `q - 1` (1008 is
        // not a multiple of 10), where every power is computed on its own.
        let q = BigUint::from(1009u32);
        assert_eq!(
            lucas_powers(&BigUint::from(5u32), &q, &[]),
            (vec![], BigUint::one())
        );
        check_lucas_powers(&BigUint::from(5u32), &q, &[2u32, 5].map(BigUint::from));
        check_lucas_powers(&BigUint::from(5u32), &q, &[5u32].map(BigUint::from));
        // Factors that are not coprime, or repeated, still have a product dividing `q - 1`.
        let q = BigUint::from(65_537u32);
        check_lucas_powers(&BigUint::from(3u32), &q, &[2u32, 4].map(BigUint::from));
        check_lucas_powers(&BigUint::from(3u32), &q, &[2u32, 2].map(BigUint::from));
        check_lucas_powers(&BigUint::from(3u32), &q, &[4u32, 2, 8].map(BigUint::from));
        // `q = 1` and `q = 2` have the exponents 0 and 1.
        check_lucas_powers(
            &BigUint::from(3u32),
            &BigUint::one(),
            &[1u32].map(BigUint::from),
        );
        check_lucas_powers(&BigUint::from(3u32), &BigUint::from(2u32), &[]);
    }

    #[test]
    fn miller_rabin_rejects_composites_with_a_valid_witness() {
        assert_eq!(miller_rabin(&BigUint::zero()), Err(0));
        assert_eq!(miller_rabin(&BigUint::one()), Err(0));
        assert_eq!(miller_rabin(&BigUint::from(4u32)), Err(2));
        assert_eq!(miller_rabin(&big("1000000000000000000000006")), Err(2));
        // Carmichael numbers, strong pseudoprimes to base 2, prime powers and products.
        let small = [
            (561u64, 2u64),
            (1105, 2),
            (1729, 2),
            (2047, 3),
            (3277, 3),
            (9, 2),
            (25, 2),
            (341, 2),
            (1_000_003 * 1_000_003, 2),
        ];
        for (n, witness) in small {
            let n = BigUint::from(n);
            assert_eq!(miller_rabin(&n), Err(witness), "{n}");
            assert!(is_witness(&n, witness), "{n}");
        }
        let big_composites = [
            "1000000000100000000002379", // (10^12 + 39)(10^12 + 61), 25 digits
            "340282366920938463463374607431768211457", // 2^128 + 1 = 59649589127497217 · 5704689200685129054721
            "5316911983139663487003542222693990401", // (2^61 - 1)^2, above the deterministic bound
            "115792089237316195423570985008687907853269984665640564039457584007913129639935", // 2^256 - 1
        ];
        for n in big_composites {
            let n = big(n);
            let witness = miller_rabin(&n).expect_err("composite");
            assert!(witness >= 2, "{n}: {witness}");
            assert!(is_witness(&n, witness), "{n}: {witness}");
        }
    }

    #[test]
    fn perfect_power_finds_a_prime_exponent() {
        assert_eq!(
            perfect_power(&big("18446744073709551616")), // 2^64
            Some((big("4294967296"), 2))
        );
        assert_eq!(perfect_power(&big("243")), Some((big("3"), 5)));
        let p = big("10000000000000000051"); // a 20-digit prime
        assert_eq!(perfect_power(&(&p * &p)), Some((p.clone(), 2)));
        assert_eq!(perfect_power(&(&p * &p * &p)), Some((p.clone(), 3)));
        assert_eq!(perfect_power(&(&p * &p * 3u32)), None);
        assert_eq!(perfect_power(&big("4")), Some((big("2"), 2)));
        assert_eq!(perfect_power(&big("8")), Some((big("2"), 3)));
        assert_eq!(perfect_power(&big("32")), Some((big("2"), 5)));
        assert_eq!(perfect_power(&big("64")), Some((big("8"), 2)));
        let non_powers = [
            "0",
            "1",
            "2",
            "3",
            "6",
            "10",
            "244",
            "18446744073709551615",      // 2^64 - 1
            "18446744073709551617",      // 2^64 + 1
            "1000000000000000000000007", // a prime
        ];
        for n in non_powers {
            assert_eq!(perfect_power(&big(n)), None, "{n}");
        }
    }

    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    struct Wrapped {
        #[serde(with = "crate::arith::big_str")]
        one: BigUint,
        #[serde(with = "crate::arith::big_str_vec")]
        many: Vec<BigUint>,
    }

    #[test]
    fn big_str_round_trips_decimal_strings() {
        let wrapped = Wrapped {
            one: big("1000000000000000000000007"),
            many: vec![BigUint::zero(), big("18446744073709551616")],
        };
        let json = serde_json::to_string(&wrapped).unwrap();
        assert_eq!(
            json,
            r#"{"one":"1000000000000000000000007","many":["0","18446744073709551616"]}"#
        );
        assert_eq!(serde_json::from_str::<Wrapped>(&json).unwrap(), wrapped);
        let empty = Wrapped {
            one: BigUint::zero(),
            many: vec![],
        };
        let json = serde_json::to_string(&empty).unwrap();
        assert_eq!(json, r#"{"one":"0","many":[]}"#);
        assert_eq!(serde_json::from_str::<Wrapped>(&json).unwrap(), empty);
        let bad = [
            r#"{"one":"","many":[]}"#,
            r#"{"one":"+1","many":[]}"#,
            r#"{"one":" 1","many":[]}"#,
            r#"{"one":"1_0","many":[]}"#,
            r#"{"one":1,"many":[]}"#,
            r#"{"one":"1","many":["1a"]}"#,
            r#"{"one":"1","many":[2]}"#,
        ];
        for text in bad {
            assert!(serde_json::from_str::<Wrapped>(text).is_err(), "{text}");
        }
    }
}
