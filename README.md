# Anodized by example

Examples of Rust specifications written with Anodized, translated to Lean with
[Charon and Aeneas](https://github.com/AeneasVerif/aeneas), and checked with Lean.

## Setup and verification

Install Git, curl, tar, Rust through [rustup](https://rustup.rs/), and Lean's
[elan](https://github.com/leanprover/elan). From the repository root run:

```sh
./scripts/aeneas-install.sh
./scripts/aeneas-translate.sh
lake exe cache get
lake build
```

The installer downloads the Aeneas release pinned in `lakefile.toml`, including
Charon, and installs the Rust toolchain required by its driver. The project
`lean-toolchain` must match the one in that release. `Cargo.lock` and
`lake-manifest.json` pin the Rust and Lean dependencies. Regenerate and commit
translations after changing an example, its dependencies, or the Aeneas pin.

The translation script discovers crates under `examples/` and writes their Lean
files and translation manifests to `examples/<crate>/translation/`. The
`*External.lean` files currently contain generated templates and axioms; the
script refuses to overwrite them if their generated header is removed for a
handwritten model. CI regenerates the translations, checks that the checkout is
unchanged, and builds the Lean libraries and proofs.

## Scope of the proofs

The Lean build checks the stated theorems against the generated translation and
its external assumptions; it does not prove every Rust item. In particular,
the binary-search proof in `Proofs/e02.lean` is incomplete, and
`Proofs/SliceIterExternal.lean` states axioms for external operations. These
assumptions are part of the trust boundary.
