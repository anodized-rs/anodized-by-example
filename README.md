# Anodized by Example

Examples of Rust specifications written with Anodized, translated to Lean with
[Charon and Aeneas](https://github.com/AeneasVerif/aeneas), and checked with Lean.

## Setup

Install Git, curl, tar, Rust through [rustup](https://rustup.rs/), and Lean's
[elan](https://github.com/leanprover/elan). From the repository root run:

```sh
./scripts/aeneas-install.sh
```

The installer uses the Aeneas release pinned in `lakefile.toml` and its matching
Rust toolchain.
