# nfield

`nfield` is a small C program for computing finite digit-field invariants:
fractional fields, alignment statistics, spectral bins, coherence
decompositions, and collision-table identities.

This public repository contains the source code, verifier, and regression tests
for the public command surface used on [alexpetty.com](https://alexpetty.com).
Papers and draft manuscripts are not distributed in this repository.

## Build

Linux / macOS:

```bash
make
```

Windows users can build through WSL:

```bash
sudo apt update
sudo apt install gcc make
make
```

## Test

```bash
make test
```

The test target builds the C unit tests, verifier-backed checks, and CLI
regression tests.

## Usage

```bash
./nfield field 7
./nfield align 12
./nfield spectral 13
./nfield decompose 21
./nfield collision_table 10
./nfield verify antisymmetry
```

## Repository Layout

```text
src/      C source for the command-line program and core computations
test/     unit and CLI regression tests
verify/   verifier-backed checks for structural identities
```

## License

MIT

## Author

Alexander S. Petty  
[alexpetty.com](https://alexpetty.com)
