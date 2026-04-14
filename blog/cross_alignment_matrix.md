# The Cross-Alignment Matrix

What if you could see the inside of an integer?

Not its size. Not its prime factorization. Something more internal. How the fractions with that integer in the denominator hold together with each other. Which ones agree, which ones disagree, which ones are strangers, which ones are kin. The picture of an integer's interior life.

The previous papers in this series measured that interior with a single number, the alignment $\alpha(n)$, which compares every fraction to $1/n$ and averages the result. A single scalar. One number per integer. Useful, but flat. It tells you how much agreement there is in the field, not where it lives.

The last paper, [the coherence decomposition](https://alexpetty.com/the-coherence-decomposition/), began to crack that scalar open. It split $\alpha = F + \sigma$ into a focused part and a background part, and the split was enough to explain the golden gap at $p = 3$. The coherence post sketched the matrix that lives behind the decomposition by working out a digit-partitioning case as a side observation. This paper picks the matrix up from there and makes it the central object.

Don't average. Keep the map.

## The floor at $p = 7$

[The coherence decomposition post](https://alexpetty.com/the-coherence-decomposition/) derived the cross-alignment matrix at $p = 11$ in full detail by comparing pairs of fractions digit by digit and walking through the off-diagonal and diagonal entries one at a time. The result was the $10 \times 10$ identity matrix. The same lesson holds at every digit-partitioning prime in base $10$, including the smaller and more famous prime $7$, where the repeating block of $1/7$ is the iconic $142857$. If you want the full pair-by-pair derivation, the coherence post is the place to read it. Here is the same fact at $p = 7$ from a different angle, the angle that connects this matrix to the nines complement that powered the [three-tier theorem](https://alexpetty.com/the-three-tier-theorem/).

Take $1/7$ and $6/7$, the partners under the nines complement. Their repeating blocks are $142857$ and $857142$. Walk down them and look at the sums of the digits at each position. $1 + 8 = 9$. $4 + 5 = 9$. $2 + 7 = 9$. $8 + 1 = 9$. $5 + 4 = 9$. $7 + 2 = 9$. Every position sums to nine. The two fractions are exact mirror images of each other in the digit system. Whenever $k$ and $n - k$ are paired, their repeating decimals are nines complements like this at every position.

The mirror property forces them to disagree everywhere. For $1/7$ and $6/7$ to share a digit at any position, both digits would have to be a number whose double is nine, and there is no such single digit. The same kind of obstruction applies to every other distinct pair. The only matches anywhere among the fractions of $7$ are the trivial matches of each fraction with itself.

So the cross-alignment matrix of $7$ is the $6 \times 6$ identity, with the diagonal of ones coming from each fraction matching itself and the off-diagonal of zeros coming from the nines complement obstruction.

```
     1/7  2/7  3/7  4/7  5/7  6/7
1/7 [  1    0    0    0    0    0  ]
2/7 [  0    1    0    0    0    0  ]
3/7 [  0    0    1    0    0    0  ]
4/7 [  0    0    0    1    0    0  ]
5/7 [  0    0    0    0    1    0  ]
6/7 [  0    0    0    0    0    1  ]
```

I will write this matrix $\mathbf{A}(7)$. It is the simplest possible matrix of its size, the matrix linear algebra calls the identity. It is the floor of the program. Every other prime gives a matrix with more structure than this, and the rest of this paper explores what those richer matrices look like.

## The strangers meet

Push to $p = 13$. Now there are twelve fractions and the same ten possible digits to share. By the pigeonhole principle, some pairs must share digits at some positions. The matrix is no longer empty.

```
 1/13 = 0.|076923|     7/13 = 0.|538461|
 2/13 = 0.|153846|     8/13 = 0.|615384|
 3/13 = 0.|230769|     9/13 = 0.|692307|
 4/13 = 0.|307692|    10/13 = 0.|769230|
 5/13 = 0.|384615|    11/13 = 0.|846153|
 6/13 = 0.|461538|    12/13 = 0.|923076|
```

Look at the leading digits across all twelve fractions: 0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9. The digit 3 appears twice. The digit 6 appears twice. Two collisions at position 1 alone. Each collision becomes a nonzero entry in the matrix at the corresponding off-diagonal cell.

But the nonzero entries are not scattered randomly. Look at the repetends in the two columns above. The first six fractions ($1/13$ through $6/13$) are cyclic rotations of `076923`. The last six ($7/13$ through $12/13$) are rotations of `538461`. Two distinct strings, six rotations of each, twelve fractions in total. Two parallel orbits through the residues, each a cycle of length six.

Fractions within the same orbit share more digits because their repetends are rotations of the same string. The matrix develops two **bright blocks** on the diagonal, one for each orbit, with dimmer entries between them.

The field of 13 has internal structure that the field of 7 does not. The matrix makes that structure visible. The single scalar $\sigma(13)$ averages it away into one number; the matrix preserves it.

## The blocks

At composites the blocks become even cleaner. Take $n = 12$:

```
  1/12 = 0.08|3|    (mixed)
  2/12 = 0.1|6|     (mixed)
  3/12 = 0.25       (terminating)
  4/12 = 0.|3|      (closed)
  5/12 = 0.41|6|    (mixed)
  6/12 = 0.5        (terminating)
  7/12 = 0.58|3|    (mixed)
  8/12 = 0.|6|      (closed)
  9/12 = 0.75       (terminating)
 10/12 = 0.8|3|     (mixed)
 11/12 = 0.91|6|    (mixed)
```

Three kinds of fractions. The terminating ones ($3/12, 6/12, 9/12$) have no repeating block. There are no repeating digits to disagree on, so among themselves they agree by absence. The fractions whose repetend is "3" ($1/12, 4/12, 7/12, 10/12$) all share the same single repeating digit. Perfect agreement within that group. The fractions whose repetend is "6" ($2/12, 5/12, 8/12, 11/12$) are the same. Perfect agreement within their group.

But a fraction repeating 3 and a fraction repeating 6 share nothing. Different digit, different group, no overlap.

The matrix of 12 is **three solid blocks of light on the diagonal, separated by darkness**. One block for the terminating fractions. One block for the 3s. One block for the 6s. Within each block, every entry is 1. Between blocks, every entry is 0. The structure is sharp.

The prime $3$ determines that there are three blocks. The smooth factor $4$ determines the size of each block (one block of size $3$ for the terminating fractions, two blocks of size $4$ for the repeating ones). The structure comes from the prime. The resolution comes from the smooth factor.

The paper proves this in general. For an integer of the form $n = ps$, where $p$ is a digit-partitioning prime and $s$ is smooth in the base, the cross-alignment matrix decomposes into exactly $p$ blocks of all-ones, with one block of size $s - 1$ (for the terminating fractions) and $p - 1$ blocks of size $s$ (one for each non-terminating residue class). Inside each block every entry is $1$. Outside the blocks every entry is $0$. The matrix has rank exactly $p$, no matter how smooth $s$ becomes. The null space grows with $s$ because every fraction in a same-repetend class is a rank-$1$ copy of the others.

Three primes, three block patterns. At $p = 7$ (digit-partitioning, repetend length $6$), every fraction sits in its own class. The matrix is the identity. Six rank-$1$ blocks of size $1$, total rank $6$. At $p = 13$ (not digit-partitioning, repetend length $6$), there are two orbits and the blocks soften by partial off-diagonal structure. At $n = 12 = 3 \cdot 4$ (digit-partitioning prime $3$ with smooth factor $4$), there are three solid blocks of sizes $3$, $4$, $4$, total rank $3$.

Three integers, three matrix shapes, three different ways of holding their interior together.

## The chord

Here is where the matrix begins to speak in a language beyond blocks and zeros.

Think of a musical chord. A chord is a sum of pure tones. Each tone has a frequency and a volume. If every tone is equally loud, you hear something close to white noise. No structure, no pattern. If one tone dominates, you hear that one as a note. If a few tones cluster at related frequencies, you hear harmony. The shape of the volume distribution across frequencies *is* the character of the sound.

A matrix has something analogous. Its **eigenvalues** are the volumes of its individual tones. They tell you which patterns are strong and which are weak. The identity matrix at $p = 7$ has every eigenvalue equal to 1. Every tone equally loud, no pattern standing out. That is total independence, heard as a perfectly balanced chord with no melody.

When the matrix gains structure, the eigenvalue distribution changes. At $p = 13$, computation shows the matrix has just two distinct eigenvalues, $4/3$ and $2/3$, each with multiplicity 6. Two notes, both played at high volume, nothing else. The harmonic portrait of $p = 13$ is a two-tone chord.

At $p = 17$, the matrix has nine distinct eigenvalues spread between $0.25$ and $1.75$. Nine separate tones, each at a different volume. A more complex harmonic portrait. The field of 17 has finer internal structure than the field of 13.

For primes where 10 is a primitive root, the paper proves something striking. The matrix is permutation-similar to a **circulant**, a special kind of matrix whose rows are cyclic shifts of each other. Circulants have a famous property. Their eigenvalues are exactly the discrete Fourier transform of their first row. So for primitive-root primes, the eigenvalue spectrum of $\mathbf{A}(p)$ is the Fourier transform of the cyclic autocorrelation of the base repetend.

In plain language, the harmonic portrait of the field, the volumes of its musical tones, are the Fourier coefficients of how the repetend echoes itself. The coherence geometry of the field is a frequency spectrum, and the digit-partitioning property is the special case where the spectrum is flat.

This is where I plan to pick up next. Once you know the matrix is a circulant, the eigenvalues are not just a list of numbers; they are the discrete Fourier transform of something concrete. My current line of attack is to take that observation and try to build a theory of what those Fourier coefficients are and why they take the values they do. If that works out, the matrix will turn out to be the bridge from counting digits to doing harmonic analysis on the field.

## The matrix is the object

If you average the cross-alignment matrix in different ways, you recover the scalars from the previous papers. Average the off-diagonal entries and you get $\sigma$, the pairwise alignment. Add a diagonal contribution and you get $\alpha$, the alignment with $1/n$. Subtract and you get $F$, the focused alignment. The $\alpha = F + \sigma$ decomposition is just two different ways of slicing the matrix.

The scalars are useful summaries. But they are summaries. The matrix is the thing.

At $p = 7$, the matrix is the identity. The scalars say "$\sigma(7) = 0$, $\alpha(7) = 1/6$, $F(7) = 1/6$." Three numbers. The matrix says, in its own language, that every fraction is a stranger to every other, total independence, six rank-1 blocks of size 1. The matrix is more informative.

At $p = 13$, the scalars say "$\sigma(13) = $ small positive, $\alpha(13) = $ slightly larger." Two numbers. The matrix says two orbits, eigenvalues $4/3$ and $2/3$, two-tone harmonic portrait, internal structure that the digit-partitioning regime doesn't have. Again the matrix wins.

At $n = 12$, the scalars say "$\sigma(12) = 3/11$, $\alpha(12) = 7/11$, $F(12) = 4/11$." Three rationals. The matrix says three solid blocks of sizes 3, 4, 4, rank 3, the structure of the prime 3 imposed at the resolution of the smooth factor 4. The matrix tells you not just *how much* coherence there is but *how it is organized*.

If you could see the cross-alignment matrix as a grid of light, the diagonal would be a clean bright line where every fraction knows itself. The blocks would glow where fractions recognize each other. The voids between blocks would be dark, marking the borders between strangers. And the eigenvalues would be the volumes of the harmonic tones the whole pattern produces when you read it as a chord.

The scalars average that landscape into one brightness value. The matrix keeps the landscape.

## A note from 2026

*April 2026*

The cross-alignment matrix introduced in this paper became the structural prequel to the boundary alphabet of the recent collision invariant program. The same finite signed table on the same multiplicative group, with the same complement involution, indexed by the same residue classes; only the signal is different. Where the alignment matrix records digit matches between fractions, the boundary alphabet of the [collision invariant](https://alexpetty.com/the-collision-invariant/) records the collision count of the digit function under multiplication by a fixed multiplier. Both are matrices on the units of $\mathbb{Z}/n\mathbb{Z}$. Both have antisymmetric structure under the complement. Both unify into one object whose decomposition is the central content of the program.

The block structure proved here for digit-partitioning $n = ps$ is the structural backbone of the recent [collision periodic table](https://alexpetty.com/the-collision-periodic-table/). The collision invariant table at conductor $b^2$ has an analogous block structure, where each "block" corresponds to a residue class and the antisymmetry under the complement involution forces the table's mean to be exactly $-1/2$. The local block structure of the alignment matrix is the local instance; the global table structure of the boundary alphabet is the generalization. Both come from the same complement reflection on the multiplicative group.

The harmonic portrait observation, that for primitive-root primes the matrix is permutation-similar to a circulant whose eigenvalues are the DFT of the cyclic autocorrelation, becomes the central object of the next several papers in the chain. The [spectral structure](https://alexpetty.com/the-spectral-structure-of-fractional-fields/), [spectral power](https://alexpetty.com/the-spectral-power-of-the-digit-function/), and [autocorrelation formula](https://alexpetty.com/the-autocorrelation-formula/) papers develop the spectral theory of this matrix in detail, eventually closing the formula chain from the digit function to the eigenvalue spectrum of $\mathbf{A}(p)$.

The fact that scalar invariants ($\alpha$, $\sigma$, $F$) are projections of a single matrix is the same observation, in different language, that the recent [collision spectrum](https://alexpetty.com/the-collision-spectrum/) makes about the boundary alphabet. The table is one object. Its various scalar reductions (mean, variance, Fourier coefficients, L-value moments) are all different ways of reading the same structural information. The matrix is the thing. The scalars are summaries.

.:.

---

## Try it yourself

Three fields, three matrix shapes:

```
$ ./nfield field 7     # identity matrix: total independence
$ ./nfield field 13    # two orbits: softened blocks, partial structure
$ ./nfield field 12    # three solid blocks: composite resolution
```

At $p = 7$, read down any column of digits in the repetends and notice that no two fractions share a digit at the same position. At $p = 13$, look for shared digits across fractions and notice they cluster within the two groups of six. At $n = 12$, sort the fractions by their repeating digit (3 vs 6 vs terminating) and the three blocks become visible.

To see the eigenvalues directly:

```
$ ./nfield spectrum 7    # all eigenvalues = 1
$ ./nfield spectrum 13   # eigenvalues 4/3 and 2/3, each with multiplicity 6
$ ./nfield spectrum 17   # nine distinct eigenvalues from 0.25 to 1.75
$ ./nfield spectrum 12   # rank 3, blocks of sizes 3, 4, 4
```

The matrix is the object the scalars are summaries of. Once you can see it, the scalars become projections of a richer structure underneath.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Cross-Alignment Matrix](https://github.com/alexspetty/nfield/blob/main/research/cross_alignment_matrix.pdf)

---

*Alexander S. Petty*
April 2021
.:.
