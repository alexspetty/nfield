# The Spectral Structure of Fractional Fields

The cross-alignment matrix at $p = 7$ has every eigenvalue equal to 1. At $p = 13$, exactly two distinct eigenvalues. At $p = 17$, nine. The eigenvalues encode the matrix's internal structure, and the structure changes with the prime. The question is what determines them.

At certain primes, an unexpected simplification appears. If you reorder the fractions by their position in the remainder cycle instead of by size, the cross-alignment matrix becomes a **circulant**: each row is the row above it, shifted by one. Circulants have a classical property. Their eigenvalues are the discrete Fourier transform of their first row.

So the question becomes: what is that first row? The answer is the cyclic autocorrelation of the repeating block of $1/p$.

## The autocorrelation

Take the repeating decimal of $1/p$ in base 10. Compare it with a shifted copy of itself. At shift $0$, every position agrees with itself. At other shifts, some positions may agree and some may not. Count the agreements for each shift. That list of counts is the **cyclic autocorrelation**.

For primitive-root primes, the first row of the reordered cross-alignment matrix is exactly that autocorrelation, divided by the cycle length. The eigenvalues are therefore the Fourier transform of the autocorrelation.

So the spectral problem has been reduced to a finite combinatorial one:

- start with the repeating block of $1/p$
- compute its cyclic autocorrelation
- take a Fourier transform
- read off the eigenvalues

That is the bridge from digit patterns to harmonic analysis.

## The flat case: $p = 7$

The repeating block of $1/7$ is

```text
142857
```

Compare it with its cyclic shifts. At shift $0$, all six positions match, so the autocorrelation entry is $6$. At every nonzero shift, no positions match, so the other entries are all $0$:

```text
shift:    0  1  2  3  4  5
matches:  6  0  0  0  0  0
```

This is the simplest possible autocorrelation: one spike at zero and nothing else.

Its Fourier transform is therefore constant. All eigenvalues of the cross-alignment matrix are equal to $1$. This matches the direct computation from [The Cross-Alignment Matrix](https://alexpetty.com/the-cross-alignment-matrix/): for the digit-partitioning prime $7$, the cross-alignment matrix is the identity.

![From autocorrelation to eigenvalues](https://alexpetty.com/content/images/2026/04/spectral_structure_pipeline.png)

At $p = 7$, nothing is hidden. The autocorrelation is a delta spike, the spectrum is flat, and the matrix is the identity.

## The two-coset case: $p = 13$

The next interesting case is $p = 13$.

Here base 10 is **not** a primitive root, so the circulant theorem does not apply directly to the full $12 \times 12$ matrix. Instead, the fractions split into two cosets of size $6$, and the paper treats that case separately.

Inside each coset, the same trivial pattern holds as at $p = 7$: distinct rotations do not match at common positions. The new feature is in the cross-coset matches. Each fraction in one coset has exactly one partner in the other coset, and that partner matches it in exactly $2$ of the $6$ positions. All other cross-coset comparisons give zero.

That forces the matrix to have the form

$$\mathbf{A}(13) = \mathbf{I} + \frac{1}{3}\mathbf{P}$$

where $\mathbf{P}$ is an involution pairing each fraction with its unique cross-coset partner.

Once the matrix has that form, the spectrum is forced. An involution has eigenvalues $\pm 1$, so the eigenvalues of $\mathbf{A}(13)$ are:

$$1 + \frac{1}{3} = \frac{4}{3}$$

and

$$1 - \frac{1}{3} = \frac{2}{3}$$

each with multiplicity $6$.

So the first nontrivial spectrum is still highly rigid. Twelve eigenvalues, but only two distinct values.

## The three regimes

These examples already show the main taxonomy.

**Digit-partitioning primes.**  
The cross-alignment matrix is the identity. The autocorrelation has a single spike. The spectrum is flat, with every eigenvalue equal to $1$.

**Two-coset primes.**  
The matrix splits into two identity-type blocks with a rigid cross-coset pairing. The spectrum collapses to two levels.

**Primitive-root primes with nontrivial autocorrelation.**  
The matrix is circulant after reordering, but the autocorrelation is no longer a delta spike. Its Fourier transform spreads across several values, and the spectrum becomes genuinely structured.

The smallest base-10 example of that third regime is $p = 17$. There the eigenvalues are no longer all equal and no longer confined to two levels.

![The three spectral regimes](https://alexpetty.com/content/images/2026/04/spectral_structure_regimes.png)

The point is not that every prime has a different spectrum. The point is that the spectrum reflects the orbit structure of the base modulo the prime.

## The three regimes

The scalar quantities $\alpha$, $\sigma$, and $F$ summarize the same field in coarser ways. The matrix keeps the full pairwise geometry. The spectrum goes one step further. It organizes that geometry into independent modes.

For primitive-root primes, those modes are exactly the additive characters of the cyclic group $\mathbb{Z}/L\mathbb{Z}$, where $L$ is the repetend length. The eigenvalues are the projections of the autocorrelation onto those characters.

That is the real content of the paper. The eigenvalues are not arbitrary numerical features of the matrix. They are a character expansion of a finite combinatorial object built from the repeating digits of $1/p$.

This is the point where the program stops being only about counting digit matches and starts becoming harmonic analysis on a finite group.

A table built from repeating decimals turns out to carry a Fourier spectrum. The spectral data was already sitting inside the digits; the matrix only makes it visible.

---
## A note from 2026

*April 2026*

This is the paper where the matrix first becomes unmistakably spectral. [The Cross-Alignment Matrix](https://alexpetty.com/the-cross-alignment-matrix/) gives the object; this paper identifies the eigenvalues as Fourier data coming from a finite autocorrelation. After that step, the harmonic language is no longer metaphorical. It is the natural language of the problem.

Two consequences followed from it. [The Spectral Power of the Digit Function](https://alexpetty.com/the-spectral-power-of-the-digit-function/) moves from the eigenvalues to the magnitude profile of the digit bins, and [The Autocorrelation Formula](https://alexpetty.com/the-autocorrelation-formula/) returns to the autocorrelation itself and makes it explicit. The same pattern eventually reappears in [The Collision Spectrum](https://alexpetty.com/the-collision-spectrum/), where a finite arithmetic table is again expanded in a natural character basis.

The case $p=13$ also aged well. At first it looks like an exception between the flat spectrum at $7$ and the richer primitive-root examples. In hindsight it is an early model of a recurrent theme: a rigid involution forcing a two-level spectral picture.

.:.

---

## Try it yourself

Start with the three basic cases:

```text
$ ./nfield spectrum 7
  eigenvalues: 1, 1, 1, 1, 1, 1

$ ./nfield spectrum 13
  eigenvalues: 4/3 (mult 6), 2/3 (mult 6)

$ ./nfield spectrum 17
  eigenvalues: nine distinct values
```

At $p = 7$, the spectrum is flat. At $p = 13$, it has two levels. At $p = 17$, it spreads out.

Now look back at the decimal expansions:

```text
$ ./nfield field 7
$ ./nfield field 13
$ ./nfield field 17
```

The spectrum is not coming from nowhere. It is coming from how the repeating blocks agree with their own shifts, and from how the fractions split into orbits under multiplication by the base.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)  
Paper: [The Spectral Structure of Fractional Fields](https://github.com/alexspetty/nfield/blob/main/research/spectral_structure.pdf)

---

*Alexander S. Petty*  
July 2021 (updated April 2026)  
.:.
