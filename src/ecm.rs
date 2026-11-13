//! ECM on Montgomery curves (stage 1 and a baby-step/giant-step stage 2) and the level table.

use num_integer::Integer;
use num_traits::{One, Zero};

use crate::arith::{gcd, mulmod, nontrivial_divisor, primes_in, BigUint};

/// One ECM effort level.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EcmLevel {
    /// The number of decimal digits of the factors this level is tuned for.
    pub digits: u32,
    /// The stage 1 bound.
    pub b1: u64,
    /// The stage 2 bound.
    pub b2: u64,
    /// The number of curves run at this level.
    pub curves: u32,
    /// The number of curves per task.
    pub curves_per_task: u32,
}

/// The ECM level table, one row per factor size, with `b2 = 100 b1`.
pub fn default_levels() -> Vec<EcmLevel> {
    const TABLE: [(u32, u64, u64, u32, u32); 6] = [
        (15, 2_000, 200_000, 25, 5),
        (20, 11_000, 1_100_000, 90, 3),
        (25, 50_000, 5_000_000, 300, 1),
        (30, 250_000, 25_000_000, 700, 1),
        (35, 1_000_000, 100_000_000, 1800, 1),
        (40, 3_000_000, 300_000_000, 5100, 1),
    ];
    TABLE
        .iter()
        .map(|&(digits, b1, b2, curves, curves_per_task)| EcmLevel {
            digits,
            b1,
            b2,
            curves,
            curves_per_task,
        })
        .collect()
}

/// A point of a Montgomery curve in projective x-only coordinates `(X : Z)`, both reduced
/// modulo the curve's modulus.
#[derive(Clone, Debug)]
struct Point {
    x: BigUint,
    z: BigUint,
}

/// `a + b mod m` for `a, b < m`.
fn add_mod(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    let sum = a + b;
    if sum >= *m {
        sum - m
    } else {
        sum
    }
}

/// `a - b mod m` for `a, b < m`.
fn sub_mod(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    if a >= b {
        a - b
    } else {
        m - b + a
    }
}

/// A Montgomery curve `B y² = x³ + A x² + x` modulo `m`, given by `a24 = (A + 2) / 4`.
struct Curve<'a> {
    m: &'a BigUint,
    a24: BigUint,
}

impl Curve<'_> {
    /// `[2]P`.
    fn double(&self, p: &Point) -> Point {
        let m = self.m;
        let s = add_mod(&p.x, &p.z, m);
        let d = sub_mod(&p.x, &p.z, m);
        let ss = mulmod(&s, &s, m);
        let dd = mulmod(&d, &d, m);
        let t = sub_mod(&ss, &dd, m);
        let x = mulmod(&ss, &dd, m);
        let z = mulmod(&t, &add_mod(&dd, &mulmod(&self.a24, &t, m), m), m);
        Point { x, z }
    }

    /// `P + Q` from `P`, `Q` and `P - Q`.
    fn add(&self, p: &Point, q: &Point, diff: &Point) -> Point {
        let m = self.m;
        let sp = add_mod(&p.x, &p.z, m);
        let dp = sub_mod(&p.x, &p.z, m);
        let sq = add_mod(&q.x, &q.z, m);
        let dq = sub_mod(&q.x, &q.z, m);
        let u1 = mulmod(&dp, &sq, m);
        let v1 = mulmod(&sp, &dq, m);
        let sum = add_mod(&u1, &v1, m);
        let dif = sub_mod(&u1, &v1, m);
        let x = mulmod(&diff.z, &mulmod(&sum, &sum, m), m);
        let z = mulmod(&diff.x, &mulmod(&dif, &dif, m), m);
        Point { x, z }
    }

    /// `[k]P` by the Montgomery ladder (`k = 0` gives the point at infinity `(1 : 0)`).
    fn ladder(&self, p: &Point, k: u64) -> Point {
        if k == 0 {
            return Point {
                x: BigUint::one(),
                z: BigUint::zero(),
            };
        }
        // `r1 - r0 = P` throughout, and `r0` is the multiple by the bits of `k` read so far.
        let mut r0 = p.clone();
        let mut r1 = self.double(p);
        for i in (0..63 - k.leading_zeros()).rev() {
            if (k >> i) & 1 == 0 {
                r1 = self.add(&r0, &r1, p);
                r0 = self.double(&r0);
            } else {
                r0 = self.add(&r0, &r1, p);
                r1 = self.double(&r1);
            }
        }
        r0
    }
}

/// The curve and starting point of Suyama's parametrization from `sigma` modulo `m ≥ 2`, or
/// `Err(g)` with `g = gcd(16 u³ v, m) > 1` when `a24` cannot be computed.
fn suyama_curve(m: &BigUint, sigma: u64) -> Result<(Curve<'_>, Point), BigUint> {
    let sigma = BigUint::from(sigma) % m;
    let three = BigUint::from(3u32);
    let u = sub_mod(&mulmod(&sigma, &sigma, m), &(BigUint::from(5u32) % m), m);
    let v = (&sigma * 4u32) % m;
    let u3 = u.modpow(&three, m);
    let num = mulmod(
        &sub_mod(&v, &u, m).modpow(&three, m),
        &add_mod(&((&u * 3u32) % m), &v, m),
        m,
    );
    let den = (BigUint::from(16u32) * &u3 * &v) % m;
    let Some(inv) = den.modinv(m) else {
        return Err(gcd(&den, m));
    };
    let curve = Curve {
        m,
        a24: mulmod(&num, &inv, m),
    };
    let point = Point {
        x: u3,
        z: v.modpow(&three, m),
    };
    Ok((curve, point))
}

/// One ECM curve on `m` from Suyama's parametrization with `sigma ≥ 6`, with the stage 1 bound
/// `b1` and the stage 2 bound `b2`. Returns a nontrivial divisor of `m` or `None`.
pub fn ecm_curve(m: &BigUint, sigma: u64, b1: u64, b2: u64) -> Option<BigUint> {
    if m.bits() < 2 {
        return None; // `m < 2` has no nontrivial divisor and no residues to compute with
    }
    let (curve, mut point) = match suyama_curve(m, sigma) {
        Ok(setup) => setup,
        Err(g) => return nontrivial_divisor(m, g),
    };

    // Stage 1.
    for p in primes_in(2..=b1) {
        let mut power = p;
        loop {
            point = curve.ladder(&point, p);
            match power.checked_mul(p) {
                Some(next) if next <= b1 => power = next,
                _ => break,
            }
        }
    }
    let g = gcd(&point.z, m);
    if !g.is_one() {
        return nontrivial_divisor(m, g);
    }
    let mut primes = primes_in(b1 + 1..=b2).peekable();
    primes.peek()?; // no primes in `(b1, b2]`

    // Stage 2. Every prime `p ∈ (b1, b2]` is `kD ± j` with `j < D/2` odd and coprime to `D`, and
    // `[p]Q` is the point at infinity modulo a prime factor exactly when `x([kD]Q) = x([j]Q)`
    // there, which the cross product `X_{G_k} Z_j − X_j Z_{G_k}` detects.
    let d: u64 = if b2 < 1_000_000 { 210 } else { 2310 };
    let half = d / 2;
    // Baby steps `pts[i] = [2i + 1]Q` for `2i + 1 < D/2`.
    let two_q = curve.double(&point);
    let mut pts = vec![point];
    pts.push(curve.add(&two_q, &pts[0], &pts[0]));
    while 2 * pts.len() + 1 < half as usize {
        let next = curve.add(&pts[pts.len() - 1], &two_q, &pts[pts.len() - 2]);
        pts.push(next);
    }
    // Giant steps `G_k = [kD]Q`, each by a differential addition of `[D]Q`.
    let q = &pts[0];
    let k0 = (b1 / d).max(1);
    let k_last = b2.div_ceil(d) + 1;
    let dq = curve.ladder(q, d);
    let mut g_k = curve.ladder(q, k0 * d);
    let mut g_k1 = curve.ladder(q, (k0 + 1) * d);
    let mut acc = BigUint::one();
    let mut count = 0u32;
    // A prime below `D/2` rounds to `k = 0`, which has no giant step (only when `b1 < D/2`).
    while primes.next_if(|&p| (p + half) / d < k0).is_some() {}
    for k in k0..=k_last {
        let target = k * d;
        while let Some(p) = primes.next_if(|&p| (p + half) / d == k) {
            let j = p.abs_diff(target);
            // Only a prime dividing `D` fails this.
            if j >= half || j.is_even() || j.gcd(&d) != 1 {
                continue;
            }
            let bj = &pts[(j / 2) as usize];
            let t = sub_mod(&mulmod(&g_k.x, &bj.z, m), &mulmod(&bj.x, &g_k.z, m), m);
            acc = mulmod(&acc, &t, m);
            count += 1;
            if count.is_multiple_of(1000) {
                let g = gcd(&acc, m);
                if !g.is_one() {
                    return nontrivial_divisor(m, g); // `g = m` ends the curve, no backtracking
                }
            }
        }
        if primes.peek().is_none() {
            break;
        }
        let next = curve.add(&g_k1, &dq, &g_k);
        g_k = g_k1;
        g_k1 = next;
    }
    nontrivial_divisor(m, gcd(&acc, m))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    /// Whether two projective points have the same x-coordinate modulo `m`.
    fn same_x(p: &Point, q: &Point, m: &BigUint) -> bool {
        mulmod(&p.x, &q.z, m) == mulmod(&q.x, &p.z, m)
    }

    #[test]
    fn ladder_agrees_with_repeated_addition() {
        // Modulo a prime the x-only group law is exact, so `[k]P` by the ladder and by a chain of
        // differential additions have the same x-coordinate, and so do `[ab]P` and `[b]([a]P)`.
        let m = big("10000000000000000051");
        let (curve, p) = suyama_curve(&m, 11).unwrap();
        let mut chain = vec![p.clone(), curve.double(&p)];
        for k in 3..=60 {
            let next = curve.add(&chain[k - 2], &p, &chain[k - 3]);
            chain.push(next);
        }
        for k in 1..=60u64 {
            let by_ladder = curve.ladder(&p, k);
            assert!(same_x(&by_ladder, &chain[k as usize - 1], &m), "k = {k}");
            assert!(!by_ladder.z.is_zero(), "k = {k}");
        }
        let ab = curve.ladder(&p, 1_000_003 * 65_537);
        let b_of_a = curve.ladder(&curve.ladder(&p, 1_000_003), 65_537);
        assert!(same_x(&ab, &b_of_a, &m));
        assert!(same_x(
            &curve.ladder(&p, 0),
            &Point {
                x: BigUint::one(),
                z: BigUint::zero()
            },
            &m
        ));
    }

    /// `p` (12 digits) and `q` (20 digits) of the first-level tests.
    fn first_level_primes() -> (BigUint, BigUint) {
        (big("314159265359"), big("27182818284590452387"))
    }

    /// The first `sigma` in `sigmas` whose curve finds a divisor, with that divisor.
    fn first_find(
        m: &BigUint,
        sigmas: std::ops::RangeInclusive<u64>,
        b1: u64,
        b2: u64,
    ) -> Option<(u64, BigUint)> {
        sigmas
            .into_iter()
            .find_map(|sigma| ecm_curve(m, sigma, b1, b2).map(|d| (sigma, d)))
    }

    #[test]
    fn finds_a_12_digit_factor_at_the_first_level() {
        let (p, q) = first_level_primes();
        let m = &p * &q;
        let (sigma, d) = first_find(&m, 6..=40, 2000, 200_000).expect("a find in sigma 6..=40");
        assert_eq!(sigma, 10);
        assert_eq!(d, p);
        assert!(d > BigUint::one() && d < m && (&m % &d).is_zero());
    }

    #[test]
    fn finds_a_15_digit_factor_at_the_second_level() {
        let p = big("161803398874991");
        let q = big("1414213562373095048801707");
        let m = &p * &q;
        let (sigma, d) =
            first_find(&m, 6..=120, 11_000, 1_100_000).expect("a find in sigma 6..=120");
        assert_eq!(sigma, 7);
        assert_eq!(d, p);
        assert!(d > BigUint::one() && d < m && (&m % &d).is_zero());
    }

    #[test]
    fn stage_2_finds_what_stage_1_misses() {
        // `sigma = 10` finds `p` in stage 2 only, and `sigma = 28` in stage 1 already.
        let (p, q) = first_level_primes();
        let m = &p * &q;
        assert_eq!(ecm_curve(&m, 10, 2000, 2000), None);
        assert_eq!(ecm_curve(&m, 10, 2000, 200_000), Some(p.clone()));
        assert_eq!(ecm_curve(&m, 28, 2000, 2000), Some(p));
    }

    #[test]
    fn the_same_inputs_give_the_same_result() {
        let (p, q) = first_level_primes();
        let m = &p * &q;
        for sigma in [9u64, 10, 28] {
            let first = ecm_curve(&m, sigma, 2000, 200_000);
            let second = ecm_curve(&m, sigma, 2000, 200_000);
            assert_eq!(first, second, "sigma = {sigma}");
        }
    }

    #[test]
    fn inversion_failure_yields_the_common_factor() {
        // `sigma = 6` gives `u = 31`, so `16 u³ v` shares the factor 31 with `m = 31 · 1000003`.
        let s = big("1000003");
        assert_eq!(ecm_curve(&(&s * 31u32), 6, 2000, 200_000), Some(big("31")));
        // `sigma = 10` gives `u = 95 = 5 · 19`.
        assert_eq!(ecm_curve(&(&s * 19u32), 10, 2000, 200_000), Some(big("19")));
        assert_eq!(ecm_curve(&(&s * 5u32), 10, 2000, 200_000), Some(big("5")));
        // `m = 93 = 3 · 31` divides `16 · 31³ · 24`: the gcd is `m` and the curve is unusable.
        assert_eq!(ecm_curve(&big("93"), 6, 2000, 200_000), None);
    }

    #[test]
    fn a_prime_modulus_and_tiny_moduli_give_none() {
        let p = big("10000000000000000051");
        assert_eq!(ecm_curve(&p, 6, 2000, 200_000), None);
        assert_eq!(ecm_curve(&p, 7, 2000, 200_000), None);
        assert_eq!(ecm_curve(&big("1000003"), 6, 2000, 200_000), None);
        assert_eq!(ecm_curve(&BigUint::zero(), 6, 2000, 200_000), None);
        assert_eq!(ecm_curve(&BigUint::one(), 6, 2000, 200_000), None);
        assert_eq!(ecm_curve(&big("2"), 6, 2000, 200_000), None);
    }
}
