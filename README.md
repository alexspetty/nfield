# nfield

Computational engine for a research program studying the digit
function floor(br/p) and its collision structure. Twenty-three
research papers and three condensed publication drafts.

## The research program

The collision invariant measures bin coincidences under
multiplication in the digit function floor(br/p). This program
studies its algebraic, spectral, and analytic properties across
all primes and bases.

The central result is the **decomposition theorem**: the
collision spectrum factors exactly into generalized Bernoulli
numbers and diagonal character sums, encoding L-function special
values.

## Publications

- [**The Collision Invariant**](publication/the_collision_invariant.pdf) (2026)
- [**The Collision Transform**](publication/the_collision_transform.pdf) (2026)
- [**The Collision Spectrum**](publication/the_collision_spectrum.pdf) (2026)

## Software

The `nfield` engine is written in C (MIT license). It verifies
every computational claim in the papers.

```
make
./nfield 10 7       # base 10, prime 7
./nfield 10 --all   # all primes in base 10
```

## Experiments

The `experiments/` directory contains 121 C and Python programs
used to discover and verify the results.

## Author

Alexander S. Petty
alexander.petty@gmail.com
