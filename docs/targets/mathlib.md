# The Mathlib target

The default target (`src/targets/mathlib.rs`) proves `Nat.Prime N` with Mathlib's `primality`
tactic, imported by `import Mathlib.Tactic.Primality`:

```lean
example : Nat.Prime 1000003 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 166667] },
    .lucas { root := 2, primeFactors := [2, 167, 499] }])
```

## What the tactic checks

For each prime `q` it meets, starting from `N`, the tactic proves `q` by `norm_num` when
`q < 2^10`. Otherwise it takes the first entry whose `primeFactors` are the prime factors of
`q − 1` and whose `root` is a primitive root of `q` (`root ^ (q - 1) % q = 1`, and
`root ^ ((q - 1) / r) % q ≠ 1` for every listed `r`), and goes on with the listed factors. An entry
does not name its prime. So the certificate needs an entry for every prime `q ≥ 2^10` reachable
from `N` through the prime factors of `q − 1`, and we emit exactly those, each with a primitive
root (the smallest, unless a hint names another).

## Output format

- The input's entry comes first, then the others by descending prime. Factor lists are
  ascending. Each entry has its own line, indented four spaces, and the list closes with `])`.
- For `N < 1024` the proof is `by primality` alone.
- An expression input is stated in Lean syntax (`2^255-19` gives `Nat.Prime (2 ^ 255 - 19)`),
  which `norm_num` evaluates. A `^` adds `import Mathlib.Tactic.NormNum.Pow`. An exponent `e` above
  256, Lean's default `exponentiation.threshold`, adds `set_option exponentiation.threshold e in`
  before the `example`.

The page links the file to the Lean playground (`https://live.lean-lang.org/`), whose default
project is the latest Mathlib.
