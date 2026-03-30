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

## Research papers

The `research/` directory contains twenty-three papers spanning
the full arc of the program, from the alignment proportion and
the golden ratio's selection of the prime 3, through the
spectral structure of fractional fields, to the collision
transform and its connection to L-functions.

| # | Title | Date |
|---|-------|------|
| 1 | Why the Golden Ratio Selects the Prime Three | January 2020 |
| 2 | Digit-Partitioning Primes and the Alignment Formula | March 2020 |
| 3 | The Alignment Limit for All Primes | August 2021 |
| 4 | The Three-Tier Conjecture | February 2022 |
| 5 | The Coherence Decomposition | June 2022 |
| 6 | The Cross-Alignment Matrix | August 2022 |
| 7 | The Character Structure of the Collision Fluctuation | March 2023 |
| 8 | The Spectral Structure of Fractional Fields | June 2023 |
| 9 | The Spectral Power of the Digit Function | August 2023 |
| 10 | The Autocorrelation Formula | October 2023 |
| 11 | Bin Derangements and the Gate Width Theorem | April 2024 |
| 12 | Phase-Filtered Ramanujan Sums and the Spectral Gate | June 2024 |
| 13 | Silent Primes and the Variance of the Collision Count | August 2024 |
| 14 | The Collision Fluctuation Sum | October 2024 |
| 15 | The Collision Transform | February 2025 |
| 16 | The Centered Collision PNT | April 2025 |
| 17 | The Collision Transform in the Critical Strip | June 2025 |
| 18 | The Neutrality Theorem | August 2025 |
| 19 | The General Neutrality Theorem | September 2025 |
| 20 | The Double Transversality | October 2025 |
| 21 | The Spectral Repulsion | October 2025 |
| 22 | The Collision Spectrum and the L-Function Landscape | November 2025 |
| 23 | The Composite Interleaving | December 2025 |

## Publications

The `publication/` directory contains four papers
distilled from the research notes.

- **The Collision Invariant** (2026)
- **The Collision Transform** (2026)
- **The Collision Spectrum** (2026)
- **Partial Character Sums and the Collision Transform** (2026)

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
