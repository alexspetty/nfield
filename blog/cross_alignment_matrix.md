# The Cross-Alignment Matrix

Compare every fraction of a number to every other fraction, digit by digit. Record the proportion of matches for each pair. The result is a grid, and the grid has a shape that depends on the number.

That grid is the **cross-alignment matrix** $\mathbf{A}(n)$. The three scalars from [The Coherence Decomposition](https://alexpetty.com/the-coherence-decomposition/), $\alpha$, $\sigma$, and $F$, are different ways of averaging it. The matrix keeps what the averages lose.

At $p = 7$, the matrix is the identity. No two fractions share a digit at any position.

At $p = 13$, the identity is still there, but the twelve fractions split into two orbits of six. Within each orbit, some digit positions line up. Between the two orbits, none do.

At $n = 12 = 3 \times 4$, three families emerge: three terminating fractions, four fractions repeating 3, and four repeating 6. That gives three solid blocks of different sizes, with agreement inside each block and none between them.

![Three shapes](https://alexpetty.com/content/images/2026/04/cross_alignment_three_shapes-1.png)

In the digit-partitioning case $n = ps$, the prime sets the number of blocks and the smooth factor sets their size. Inside each block, every fraction is a copy of the others, so each block has rank one and the total rank is the number of blocks.

## The eigenvalue spectrum

A matrix carries more information than its entries. Its **eigenvalues** measure the independent patterns inside it. The identity matrix at $p = 7$ has every eigenvalue equal to 1.

![The chord](https://alexpetty.com/content/images/2026/04/cross_alignment_chord-1.png)

At $p = 13$, the matrix has two distinct eigenvalues: $4/3$ and $2/3$, each with multiplicity 6. At $p = 17$, there are nine distinct eigenvalues spread between $0.25$ and $1.75$.

For primes where 10 is a primitive root, the matrix is permutation-similar to a **circulant**, a matrix whose rows are cyclic shifts of one another. Circulants have a standard spectral description: their eigenvalues are the discrete Fourier transform of the first row. So in this case the eigenvalue spectrum of $\mathbf{A}(p)$ is the Fourier transform of the cyclic autocorrelation of the repetend.

This is the point where the work starts to move from digit counting toward harmonic analysis on the field.

## The matrix is the object

$\alpha$, $\sigma$, and $F$ from [The Coherence Decomposition](https://alexpetty.com/the-coherence-decomposition/) are related to this matrix, but not identically. Average the off-diagonal entries and you recover $\sigma$. The matrix captures the non-terminating pairwise structure exactly. The total alignment $\alpha$ still needs the terminating-fraction convention used in [The Coherence Decomposition](https://alexpetty.com/the-coherence-decomposition/), and then $F = \alpha - \sigma$ measures the excess coherence of $1/n$ over the pairwise background.

The earlier scalar invariants were shadows of a larger object. Once the matrix is written down, the geometry of the field is no longer hidden inside an average.
## A note from 2026

*April 2026*

The matrix turned out to be a durable object. Once it was written down, the rest of the spectral side of the work had somewhere definite to live. [The Spectral Structure of Fractional Fields](https://alexpetty.com/the-spectral-structure-of-fractional-fields/) reads its eigenvalues, [The Spectral Power of the Digit Function](https://alexpetty.com/the-spectral-power-of-the-digit-function/) isolates the magnitude side of the same Fourier data, and [The Autocorrelation Formula](https://alexpetty.com/the-autocorrelation-formula/) closes the loop by recovering the self-match counts.

The same grid idea also survives into the collision work. [The Collision Periodic Table](https://alexpetty.com/the-collision-periodic-table/) keeps the finite table but changes the signal being written into its cells. The complement symmetry remains. The block structure remains. What changes is what is being measured.

That makes this paper feel less like a side excursion than it first did. It is the point where the geometry of pairwise agreement becomes explicit enough to support everything that follows.

.:.

---

## Try it yourself

Three fields, three matrix shapes:

```
$ ./nfield field 7     # identity matrix: no off-diagonal agreement
$ ./nfield field 13    # two orbits: partial block structure
$ ./nfield field 12    # three solid blocks: composite case
```

At $p = 7$, no two fractions share a digit at the same position. At $p = 13$, shared digits cluster within the two groups of six. At $n = 12$, sorting by repeating block makes the three blocks visible.

Now look at the spectrum.

```
$ ./nfield spectral 7    # all eigenvalues = 1
$ ./nfield spectral 13   # two eigenvalues: 4/3 and 2/3
$ ./nfield spectral 17   # nine distinct eigenvalues
```

At $p = 7$, the spectrum is completely flat. At $p = 13$, there are two levels. At $p = 17$, many more levels appear.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Cross-Alignment Matrix](https://github.com/alexspetty/nfield/blob/main/research/cross_alignment_matrix.pdf)

---

*Alexander S. Petty*
April 2021
.:.
