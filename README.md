# nfield

`nfield` is my command-line tool for digit fields, alignment, collision tables,
finite character transforms, and the arithmetic that grows out of them.

I wrote it to get the calculations out of one-off programs and into something I
could query, sweep, test, and reuse. It is a tool first. The papers develop the
mathematics. `nfield` runs the calculations.

The command-line program is written in C. Integer and rational calculations
stay exact where the object permits it. Fourier sums and eigenvalue calculations
use numerical arithmetic and are marked as such in the output. The formal
proof library is written in Lean.

## Build

You need a C99 compiler, Make, POSIX threads, LAPACK, and BLAS.

On Debian, Ubuntu, or WSL:

```bash
sudo apt update
sudo apt install gcc make liblapack-dev libblas-dev
make
```

The Makefile normally finds LAPACK and BLAS on its own. If yours live somewhere
unusual, pass the linker flags directly:

```bash
make LAPACK_LIBS="-L/path/to/lib -llapack -lblas"
```

## Start here

```bash
./nfield --help
./nfield field 7
./nfield align 12
./nfield spectral 13
./nfield collision-table inspect 13 --base 10
```

The short commands are useful for walking around a fractional field:

```text
field       print the complete field for one denominator
analyze     compute its main invariants
div         print the long-division table
align       compute synchronized alignment
decompose   split the alignment into its components
spectral    compute additive spectral power
survey      scan a range of denominators
```

Base 10 is the default. Use `--base` to change it:

```bash
./nfield field 7 --base 3
./nfield align 21 --base 2
```

The larger tools use a command family followed by an action:

```bash
./nfield digit-partition inspect 6 --base 2
./nfield collision-transform spectrum --base 10 --lag 1
./nfield prime-base-collision-energy inspect 43
./nfield carry-completed-carrier seam 30
```

Run these when you need to find a command:

```bash
./nfield commands
./nfield help collision-transform
./nfield collision-transform --help
```

Most families have an `inspect` action for one object and a `verify` action for
their fixed checks. Some also have `table`, `scan`, `spectrum`, or `examples`.
The focused help prints the actual arguments.

## Main command families

Digit structure and alignment:

```text
weighted-reference-profile   digit-partition
alignment-limit              three-tier
deficit-lattice              coherence-decomposition
cross-alignment              reciprocal-square-selection
```

Collision arithmetic:

```text
bin-derangements             collision-characters
silent-primes                collision-fluctuation
collision-centering          collision-table
collision-transform          finite-determination
reflection-identity          half-group
```

Spectra and character sums:

```text
spectral-structure           spectral-power
autocorrelation              phase-gate
primitive-odd-sector         finite-character-pairing
collision-spectrum-factorization
special-value-moment         periodic-zeta-factorization
```

Residue channels and boundaries:

```text
residue-three-neutrality     compatible-residue-channels
coprime-base-orthogonality   primitive-character-cancellation
collision-boundary-recovery  active-collision-channel
finite-prefix-slice          boundary-bernoulli-factorization
boundary-conductor-ledger    finite-state-orbit-boundary
```

Energy and carrier calculations:

```text
full-orbit-energy            quadratic-orbit-energy
subgroup-jacobi-expansion    prime-base-collision-energy
arithmetic-boundary-defect   carry-completed-carrier
```

This is only a map. `./nfield commands` is the full list.

## Tab completion

Completion knows the command families, actions, help topics, verifier names,
and options.

```bash
# Bash
source <(./nfield completion bash)

# Zsh
source <(./nfield completion zsh)

# Fish
./nfield completion fish | source
```

After that, `nfield fi` followed by Tab will complete or list the matching
commands. Run `./nfield help completion` for permanent setup.

## Verification

```bash
make test
make verify
```

`make test` runs the C unit tests, command-line tests, completion tests, daemon
tests, and the paper-to-tool coverage check.

`make verify` runs every named verifier. You can run one directly:

```bash
./nfield verify collision-table
./nfield verify boundary-conductor-ledger
```

The output keeps exact finite arithmetic, numerical checks, bounded searches,
and theorem claims separate. A verifier reports what it has actually checked.

If you came here from one of the papers, use:

```bash
./nfield help reading-map
```

The longer title-to-command ledger is in
[`VERIFICATION_COVERAGE.md`](VERIFICATION_COVERAGE.md).

## Lean proofs

The public Lean library contains the formal companions through *The Secondary
Term in Digit-Collision Energy*.

```bash
cd proofs
lake build
```

The Lean toolchain and Mathlib revision are pinned in that directory. See
[`proofs/README.md`](proofs/README.md) for the boundary of the public library.

## Daemon

The website uses the same command dispatcher through a small JSON/TCP daemon:

```bash
./nfield daemon --port 9090
```

Send one JSON object per connection:

```json
{"cmd":"collision-table inspect 13 --base 10"}
```

The daemon does not invoke a shell. It returns the same text as the command-line
program.

## Version

```bash
./nfield --version
```

The version is the UTC link time written as `YYYY.MMDD.HHMMSS`. A no-op `make`
keeps the existing version. To reproduce one exactly:

```bash
make BUILD_VERSION=2026.0902.120000
```

## Source tree

```text
src/      arithmetic and command implementations
verify/   verifier registry and older fixed checks
test/     unit, CLI, completion, daemon, and coverage tests
proofs/   Lean definitions, theorems, and public paper maps
```

Commands and source files are named for the mathematical object, not for a
paper number. Papers and draft manuscripts are not part of this repository.

## License

Copyright 2020-2026 Alexander S. Petty.

The `nfield` software is available under the
[PolyForm Noncommercial License 1.0.0](LICENSE). Use it as much as you want for
research, study, education, and personal work. If you are using it to make
money, or building it into something that makes money, let's talk about a
commercial license. See
[commercial licensing](COMMERCIAL-LICENSING.md).

The Lean source in `proofs/` is authored by Alexander S. Petty and is open
source under the [Apache License 2.0](proofs/LICENSE).

Alexander S. Petty<br>
[alexpetty.com](https://alexpetty.com)
