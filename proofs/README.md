# nfield Lean proofs

This directory contains the public Lean side of `nfield`.

The nfield formalizations are authored by Alexander S. Petty and are open
source under the [Apache License 2.0](LICENSE). You may use, change, and
redistribute them under those terms, including in commercial work. Reused
upstream source retains its separate attribution and license notices.

The library builds on [Mathlib](https://github.com/leanprover-community/mathlib4),
using its mathematical definitions, existing theorems, and proof tactics.
Mathlib is installed as a pinned dependency; its source is not copied into
this package. Additional analytic number theory modules are adapted from
PrimeNumberTheoremAnd. Their authorship, source revision, exact source hashes,
and adaptations are documented in
[the upstream provenance note](NField/External/ConservationPNT/README.md).

`NField.lean` imports the paper companions. Each companion selects results
from the reusable definitions and proofs under `NField/Alignment/`,
`NField/Golden/`, and the other object-named directories.

The library contains complete and partial formalizations. Each companion
states its mathematical coverage and the hypotheses of its selected results.

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
NField/External/     attributed upstream proof inputs
```

A successful build checks the selected Lean statements and their hypotheses.
It does not extend a companion's stated mathematical coverage.
