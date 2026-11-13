# The HexPrime target

The `hexprime` target (`src/targets/hex.rs`) proves `Hex.Nat.Prime N` with the certificate checker
of Hex's [`hex-primality`](https://github.com/leanprover/hex-primality) library (release `v0.10.0`,
imported by `import HexPrimality`):

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

No online editor has the library, so the page offers no playground link.

## What the checker accepts

`Hex.Nat.prime_of_checkPrimeAt` turns a certificate that Hex's checker accepts into a proof, with
the check run by `decide +kernel`. We emit two kinds of node.
- `.small n` is accepted when `n` is in Hex's table of the primes below `100000`.
- `.pock n factors` is accepted when `n ≥ 2` is odd, the entries' primes are at least 2 and
  strictly ascending, `F = ∏ q ^ (e + 1)` over the entries `(a, e, child)` divides `n − 1`,
  `n < F * F`, and every entry has `a ^ (n − 1) % n = 1` and
  `gcd((a ^ ((n − 1) / q) % n + n − 1) % n, n) = 1`. Each child is then checked the same way.

The exponent is stored off by one, so the entry `(a, e, child)` stands for `q ^ (e + 1)`. Children
are written out in full, so a prime met twice in the tree appears twice.

Each Lucas entry becomes one `.pock` node whose factored part is all of `n − 1`. Its entries are the
prime factors of `n − 1`, each with the entry's primitive root as base and with its exact
multiplicity. A primitive root passes every condition, since `a ^ ((n − 1) / q) % n` is neither 1
nor 0, which makes the gcd's argument coprime to `n`. Every prime below `100000` becomes `.small`.

## Output format

- The certificate follows `(c := ` on the `exact` line. A `.pock n [` node puts each entry on its
  own line, indented two spaces more than the line that opened the node (four for the input's
  node), and closes with `]` and then the entry's `)`. The line `    (by decide +kernel)` ends the
  text.
- For `N < 100000` the certificate is `.small N` on the `exact` line.
- An expression input is stated in Lean syntax (`Hex.Nat.Prime (2 ^ 255 - 19)`), which the kernel
  evaluates in `decide`. The certificate's nodes keep their numerals, and no
  `exponentiation.threshold` is needed.

## Checking the texts

CI does not check this target. To check texts by hand, put the CLI's `--target hexprime` output in
one file after `import HexPrimality`, and run `lake env lean <file>` from a clone of the `v0.10.0`
release.
