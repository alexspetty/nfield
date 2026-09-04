# nfield Lean proofs

This directory contains the public Lean side of `nfield`.

These proofs are authored by Alexander S. Petty and are open source under the
[Apache License 2.0](LICENSE). You may use, change, and redistribute the Lean
source under those terms, including in commercial work.

The root module imports the formal paper maps in reading order, ending with
*The Secondary Term in Digit-Collision Energy*. The reusable definitions and
proofs under `NField/Alignment/`, `NField/Golden/`, and the other object-named
directories are included when one of those paper maps imports them.

Draft manuscripts, correspondence bundles, generated build files, and current
private work are not part of this package.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake build
```

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the Lean and
Mathlib revisions used for the build.

## Layout

```text
NField.lean          public library root
NField/Papers/       paper-facing theorem maps
NField/Alignment/    reusable alignment and collision proofs
NField/Golden/       reusable threshold and finite-orbit proofs
```

The public release check builds this root from source and rejects unchecked
declarations, private repository paths, compiled Lean files, and unpublished
paper modules.
