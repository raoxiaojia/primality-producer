# The HexPrime target

`hexprime` (`src/targets/hex.rs`, end-to-end tests in `tests/hex.rs`): `example : Hex.Nat.Prime N
:= by exact Hex.Nat.prime_of_checkPrimeAt (c := …) (by decide +kernel)`, a certificate literal for
Hex's `hex-primality` library (release `v0.10.0`), which proves the Mathlib-free
`Hex.Nat.Prime n`. No online editor has the library, so the page offers no playground link.

## Decisions (user, 2026-11-06)

- The target renders the Lucas certificate as Pocklington nodes whose factored part is all of
  `n − 1`, which is Lucas's test in Pocklington's form; nothing is searched for it.
- A search that stops once `F > √q` and emits the HexPrime certificate before the Lucas one is
  deferred until Mathlib's `primality` moves to Pocklington, which would need the same.

## The Hex side (facts the output must match)

Hex's `hex-primality` library, release `v0.10.0` (repository
`https://github.com/leanprover/hex-primality`, Lean `v4.35.0-rc3`, no Mathlib; its development
happens in `kim-em/hex-dev`). The user imports it with `import HexPrimality`. A certificate is a
literal of

```lean
inductive Hex.Nat.PrimeCert where
  | small (n : Nat)
  | pock (n : Nat) (factors : List (Nat × Nat × PrimeCert))
  | pock3 (n r s w : Nat) (factors : List (Nat × Nat × PrimeCert))
  | pock3Sieve (n r s w m : Nat) (factors : List (Nat × Nat × PrimeCert))
```

and `Hex.Nat.prime_of_checkPrimeAt {n} {c} (h : (c.subject == n && checkPrime c) = true) :
Hex.Nat.Prime n` turns an accepted literal into a proof, with `h` closed by `decide +kernel`. We
emit `small` and `pock` only. The checker (`HexPrimality/Cert.lean`) accepts:
- `.small n` when `n` is in Hex's table of the primes below `100000`;
- `.pock n factors` when `2 ≤ n`, `n` is odd, the factor entries' primes (each child's subject)
  are each at least 2 and strictly ascending, `F = ∏ q ^ (e + 1)` over the entries `(a, e, c)` divides `n − 1`,
  `n < F * F`, and every entry has `a ^ (n − 1) % n = 1` and
  `gcd((a ^ ((n − 1) / q) % n + n − 1) % n, n) = 1`; then each child is checked the same way.

The exponent is stored off by one: the entry `(a, e, c)` stands for `q ^ (e + 1)`. Each entry has
its own base `a`, and children are written out in full (a prime met twice in the tree appears
twice). For a prime `n`, a primitive root `a` passes every entry's conditions: Fermat holds, and
`a ^ ((n − 1) / q) % n` is neither 1 nor 0, so the gcd argument lies in `1 … n − 2` and is coprime
to `n`. So each Lucas entry becomes one `.pock` node whose entries are its factors, each with the
entry's root as base and its exact multiplicity in `n − 1`, and every prime below `100000` becomes
`.small`.

Hex's table covers every prime below the witness bound 1024, so the certificate has an entry for
every prime the tree needs. A certificate checked at a witness bound above `100000` can lack one,
and the target then fails with "the HexPrime target: q is at least 100000 and has no entry".

## Output format

```lean
example : Hex.Nat.Prime 1000003 := by
  exact Hex.Nat.prime_of_checkPrimeAt (c := .pock 1000003 [
    (2, 0, .small 2),
    (2, 0, .small 3),
    (2, 0, .pock 166667 [
      (2, 0, .small 2),
      (2, 0, .small 167),
      (2, 0, .small 499)])])
    (by decide +kernel)
```

Rules: the certificate follows `(c := ` on the `exact` line; a `.pock n [` node puts each factor
entry `(a, e, child)` on its own line, indented two spaces more than the line that opened the
node (four for the input's node), with the closing `]` and then the entry's `)` after its last
entry; the line `    (by decide +kernel)` ends the text. For `n < 100000` the certificate is
`.small n` on the `exact` line. Numbers are never wrapped. An expression input is stated in the
same Lean syntax (`Hex.Nat.Prime (2 ^ 255 - 19)`); the kernel evaluates it in `decide`, and the
certificate's nodes keep their numerals. Hex needs no `exponentiation.threshold`, since the
kernel evaluates the power in `decide`.

## Checks

The texts are checked by hand against `hex-primality v0.10.0`: collect the CLI's
`--target hexprime` texts in one file after the line `import HexPrimality`, and run
`lake env lean <file>` from a clone of that release.

- 22 texts (1000003, 65537 and the gallery of 2026-11-06) compiled in 25.7 s. A certificate with
  a wrong base or a wrong stored exponent fails. Net of the import, Wagstaff 2617 took 1.9 s and
  427! + 1 3.8 s (one run each).
- 5 expressions compiled in 4 s warm. Stating the Proth prime as an expression costs Hex nothing
  (4.2 s with the import, either way).

## Implementation notes (2026-11-06)

- On the 20 gallery entries of 2026-11-06 no `.pock` node is written twice (as many nodes as distinct primes
  at least 100000), so writing children out in full costs nothing there. The HexPrime text is 1.2
  to 3.7 times the Mathlib text (21 KB at most, Wagstaff 2617), longest relative to Mathlib where
  `n − 1` is smooth (the primorial 1021# + 1, one entry with many small factors).
- The tree's check (`check`, Hex's `checkPrime` without the modular conditions, which `verify`
  has shown for the same roots and factors) adds no modular arithmetic, so the `Verify` task's
  time is unchanged within noise (Wagstaff 2617 in the browser: 2.5 s, against 2.4 s before the
  target existed).

## Tests

- `targets::hex`: `from_certificate` on the certificate of `1000003` (two levels), of a prime
  below `TABLE_BOUND` (`.small`), of one whose `q − 1` has a repeated factor (exponents), of one
  meeting a prime twice (written out twice), and a missing entry (also through `TARGET.output`,
  with the target's label); `check` accepts those trees and rejects a composite `.small`, a
  `.small` at the bound, an even `n`, unsorted and repeated subjects, an exponent too large
  (`F ∤ n − 1`), an `F` too small (`n ≥ F²`), a base other than the entry's root, a subject set
  other than the entry's factors, a `.pock` with no entry, and a tree about a number other than
  `n`; the rendering of `.small` (by numeral and by expression), of a two-level tree and of a tree
  meeting one prime twice; the renderer's import.
- `tests/hex.rs`: the text of `2^127 − 1` from the driver's certificate (its exponents and its
  five `.pock` nodes). The shared tests compare the CLI's `--target hexprime` with the library's
  text.
