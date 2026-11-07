# nfield

`nfield` is a command-line tool for digit fields, alignment, collision tables
and finite character transforms.

Start with a field, change its base, or inspect a collision table. The output
distinguishes exact integer and rational results, numerical comparisons and
directed intervals.

## Build and explore

You need a C99 compiler, Make, POSIX threads, LAPACK, BLAS, GMP and MPFR.
On Debian or Ubuntu:

```sh
sudo apt install gcc make liblapack-dev libblas-dev libgmp-dev libmpfr-dev
make
./nfield field 7
./nfield align 21 --base 2
./nfield collision-table inspect 13 --base 10
```

Use `make LAPACK_LIBS="-L/path/to/lib -llapack -lblas"` if the libraries
are installed elsewhere. `make parallel` builds with OpenMP support.

```sh
./nfield commands
./nfield help collision-table
./nfield help reading-map
```

Most command families offer `inspect` and `verify`. Each command's help lists
its operations, inputs and limits.

## Grids, readings and energy

A field's boundary values are supplied separately from its one-sided traces.
The calculations include the signed cross terms between components.

```sh
./nfield field-observation clocks 4 0 1,2 0,0 1,-1
./nfield field-observation segments 4 0 0 0 1 0
./nfield field-observation pulses 5 0 1/4,1/2 3/4,1 1,1 1,1 0,0
./nfield field-observation work 1/2,1/2,0 0,1/3,2/3 1,-1,2 0,1,-1
```

Lists use commas. Fractions stay exact. A complex value uses `real:imag`,
for example `1/2:-3/4`. `segments` takes boundary locations, right traces,
slopes and actual boundary readings. It reports the regular curvature term
as well as the point and jump contributions. `harmonics` evaluates exact
Fourier aliasing at whole-cell or half-cell offsets.

```sh
./nfield collision-sampling grid 4 25 1/2
./nfield collision-sampling decomposition 31 2
./nfield collision-sampling prefix-word 8 3
./nfield collision-sampling shells 121 10
```

The sampling tools separate the common reset, signed count sources,
reciprocity costs and terminal remainders. Larger sampled carry tables use
`collision-sampling sampled`. These finite readings do not infer a limit or
a uniform power saving.


## Populations, interactions and reverse readings

```sh
./nfield collision-sampling prefix-population 5 12
./nfield collision-sampling stopped-cost 64 2
./nfield field-observation clocks 4 0 1,2 0,0 1,-1 --matrix
./nfield field-observation pulses 4 0 0,1/2 1/2,1 1,3 1,1 1,1 --matrix
./nfield field-observation harmonics 4 0 1,-3 1,0:1 --matrix
./nfield field-observation shells 1,4,8 --from-prefixes
```

`prefix-population` lists every admissible prefix of length at least two in
an inclusive denominator range, with its word, matrix and orientation. Both
orientations are included. Denominators are bounded by 512; wide listings are
best read locally. `stopped-cost` accepts a modulus through 512 and a threshold
from one through that modulus. It returns every residue, including nonunits,
and each signed cyclic jump. Its total variation includes both endpoint jumps.

`--matrix` adds continuous and sampled component Grams and their signed
matrix difference. Clocks and pulses also expose the point, value-jump and
derivative-jump matrices. Entries retain complex amplitudes, actual pulse
endpoint readings and both cross orientations. Matrix indices start at zero.
Summing every entry recovers the ordinary combined-field output; new component
coefficients act by the Hermitian quadratic form. The option follows the normal
arguments of `clocks`, `pulses` or `harmonics`.

`shells` ordinarily starts with primitive contributions. `--from-prefixes`
reverses that reading: supply square prefixes at cutoffs one through the list
length, with the zero-cutoff prefix understood to be zero. Recovery retains
signed rational values and checks the full reconstructed prefix sequence.
Either mode accepts at most 256 readings and returns the same shell and
prime-log coefficient format.

## Native refinement and complete tails

```sh
./nfield native-refinement detector 4 --json
./nfield native-refinement probe-transport 2 --json
./nfield native-refinement mask-capture 20 48 10
./nfield native-refinement divisor-work 2 64
./nfield native-refinement parent-credit 51
./nfield field-observation native-cycle 4 1,0
./nfield field-observation tail-bound 89 2 3 -1/10
```

`detector` uses complete native inner products with directed intervals.
Its response retains the signed commutator and terminal pairing.
`probe-transport` follows the same probes to four times the cutoff, retaining
the signed response drift and every entry of the old, new and removed cost
matrices. It admits cutoffs 2 through 8; start with 2 in the web tool.
`mask-capture` gives numerical rank and capture estimates for masks, address
controls and their joint span. `divisor-work` includes the removed shell and a complete
allowance for the omitted tail. `native-cycle` sums the entire native tail of
a periodic field. `tail-bound` is conditional on the supplied global envelopes.

For readings unchanged by permitted additions, `field-observation invariants`
computes their joint constrained minimum, including overlapping or complex
rows. Independent rows and positive observation weights are required.

## Conserved states and laws

`weighted-remainder-state` contains primitive mass, rational clock states,
cutoff and conductor calculations, alignment products and finite laws:

```sh
./nfield help weighted-remainder-state
./nfield weighted-remainder-state alignment-local 3 2
./nfield weighted-remainder-state law-cdf 5 -1/3 1/10
./nfield weighted-remainder-state law-characteristic 5 1
```

`capacity-resolution`, `capacity-generation` and `boundary-spectrum` provide
related observation, source and conductor operations.

## Web tool and daemon

The commands are also available in the [web tool](https://alexpetty.com/terminal).
To run the local JSON/TCP daemon:

```sh
./nfield daemon --port 9090 --threads 1
```

Send one JSON object per line, such as `{"cmd":"field 7"}`. The response
contains the command output. See `nfield help daemon` for the protocol.

## Tests

```sh
make test
make verify
```

Daemon tests need local loopback sockets.

The [Lean proof library](proofs/README.md) contains the formal statements and
instructions for checking them.

## License

The C program uses [PolyForm Noncommercial 1.0.0](LICENSE).
See [commercial licensing](COMMERCIAL-LICENSING.md) for other use.
The Lean proof library uses [Apache-2.0](proofs/LICENSE).
