# primality-producer

A static web page and a command-line tool that take a prime `n` and print a Lean `example`
proving `Nat.Prime n` with Mathlib's `primality` tactic, with the certificate the tactic checks.
They share one Rust library, compiled to WebAssembly for the page, which runs entirely in the
browser.

Each output target is a module of `src/targets/`, listed in `src/targets.rs` and documented in
[docs/targets/](docs/targets/).

## Build

Building needs Rust through rustup (`rust-toolchain.toml` pins the release) and, for the page,
[wasm-pack](https://wasm-bindgen.github.io/wasm-pack/).

- `cargo build --release` builds the command-line tool `target/release/primality-cert`.
- `scripts/build-web.sh` builds the page into `dist/`, a static site to copy to any host.
  `scripts/build-web.sh --deploy user@host:/path/to/folder` also copies it there with `scp`.

## Run

```
target/release/primality-cert <N> [--hints "<text>"] [--threads k] [--max-ecm-levels L] [--target T] [--quiet] [--json]
```

`N` is a decimal number or an expression with `+ - * ^` and parentheses such as `"2^255 - 19"`,
whose value has at most 1000 digits. The Lean file goes to stdout, and progress to stderr unless
`--quiet`. `--hints` takes known factors of `N − 1`, or of `q − 1` for a smaller prime `q` in the
certificate, and `q:a` suggests a primitive root `a` of `q`. `--json` prints the final `Snapshot`
(`src/driver.rs`) instead of the Lean file. The exit code is 0 when certified, 1 for invalid
input, 2 when `N` is composite and 3 when the run failed. A failed run prints the factors found so
far, ready to pass back as hints.

```
target/release/primality-cert 65537
target/release/primality-cert "2^127 - 1"
target/release/primality-cert 170141183460469231731687303715884105727 --hints "77158673929:11"
```

The page takes `?n=…`, `?hints=…`, `?workers=…` and `?target=…` to prefill its form. Its credits
page, `web/credits.html`, lists related projects.

## Test

- `cargo test`, `cargo clippy --all-targets` and `cargo fmt --check`.
- `node scripts/web-check.mjs` checks the page's logic without a browser. It needs Node 22 or
  later and the wasm package from `scripts/build-web.sh`.
- `python scripts/gallery/test_gallery.py` tests the gallery scripts.
- `python scripts/browser-check.py --n 65537 --expect-file 65537.lean` checks the page in headless
  Edge (`pip install playwright`) against a file the command-line tool wrote. It expects the page
  served by `python scripts/serve.py`.
- CI also compiles the Lean output for a few inputs against Mathlib master.

## Gallery

`web/gallery.json` lists special primes with hints that let each certify in about a second.
`python scripts/gallery/build_gallery.py` builds it from `scripts/gallery/entries.json` and the
hint files in `scripts/gallery/hints/`.
