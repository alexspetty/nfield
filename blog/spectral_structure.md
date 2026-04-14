# The Spectral Structure of Fractional Fields

A matrix has a voice. You hear it in its eigenvalues.

[The cross-alignment matrix](https://alexpetty.com/the-cross-alignment-matrix/) made the matrix the central object of the alignment program. It is the grid of light where the diagonal records each fraction of a prime knowing itself, and the off-diagonal records how often distinct fractions agree at the same digit position. That paper showed the matrix has a shape, that the shape varies with the prime, and that at digit-partitioning primes the shape is the simplest possible one. But it left the deeper question hanging. What does the matrix *sound like*?

## What an eigenvalue is

Eigenvalues are the answer. Every square matrix has a small finite list of numbers attached to it called its eigenvalues. For an $n \times n$ matrix the list has $n$ entries (counted with multiplicity), and the entries together capture the matrix's structural content. You will find the precise definition in any linear algebra textbook. What matters here is the metaphor.

The eigenvalues of a matrix are the volumes of its individual tones. A matrix whose eigenvalues are all equal is a flat chord with no melody. A matrix with one dominant eigenvalue is a single bright note. A matrix whose eigenvalues split into a few discrete levels is a small chord, easy to name. A matrix with eigenvalues spread across an interval is harmony.

The question this paper answers is what determines the eigenvalues of the cross-alignment matrix. Where do its tones come from? Why are they where they are? And what do they say about the prime that produced them?

## A clever reordering

The first move is unexpected. Pick a prime where the base $10$ generates the full set of nonzero residues by repeated multiplication. The technical name for this property is *primitive root*, but the only fact you need is its consequence. When $10$ is a primitive root modulo a prime $p$, every fraction $1/p, 2/p, \ldots, (p-1)/p$ turns out to be a cyclic rotation of the same repeating decimal. The smallest base-$10$ example with anything interesting going on is $p = 7$, where the six fractions $1/7$ through $6/7$ are all rotations of the famous string $142857$.

When that happens, you can do something clever with the rows and columns of the cross-alignment matrix. Instead of listing the fractions $1/p, 2/p, 3/p, \ldots$ in their natural numerical order, list them in the order their decimal expansions appear as cyclic rotations of $1/p$. The first row is $1/p$ itself. The second row is the fraction whose decimal is $1/p$ shifted one position. The third is the next shift, and so on around the cycle.

After the reordering, something unexpected happens. The matrix becomes one of the most rigid kinds of matrix in linear algebra. Its rows are no longer arbitrary; each row is the row above it shifted by one position. A matrix with that property has a name. It is a **circulant**.

Circulants are a small dynasty in linear algebra. They have been studied for over a century. They have a famous classical theorem attached to them, and the theorem says exactly the thing we want to hear: *the eigenvalues of a circulant matrix are the discrete Fourier transform of its first row*. Hand a circulant a single row of numbers, and the eigenvalues fall out as the harmonic content of that row.

So for primes where $10$ is a primitive root, computing the eigenvalues of the cross-alignment matrix reduces to two questions. What is the first row of the reordered matrix? And what do you get when you run a Fourier transform through it?

## The first row, named

The first row of the reordered matrix records, for each cyclic shift, the proportion of digit positions where the repeating decimal of $1/p$ agrees with its shifted copy. At shift zero, every position agrees with itself, so the entry at shift zero is one. At nonzero shifts, the entry is some number between zero and one, depending on how often the repetend echoes itself when slid against its own copy.

This collection of self-agreement counts has a name in classical signal processing. It is called the **cyclic autocorrelation** of the repetend. It is a small object, just a list of integers between zero and the cycle length, but it is exactly the thing the eigenvalues fall out of.

The theorem of this paper, in one sentence, is that for primes where $10$ is a primitive root, the eigenvalues of the cross-alignment matrix are the harmonic content of the autocorrelation. The grid of digit matches becomes a frequency spectrum in one Fourier transform.

That is the headline. Two more steps will show what it means.

## A flat chord at $p = 7$

The cross-alignment matrix at $p = 7$ is the $6 \times 6$ identity, derived from scratch in [the cross-alignment matrix paper](https://alexpetty.com/the-cross-alignment-matrix/). All ones on the diagonal because every fraction matches itself, all zeros off the diagonal because no two distinct fractions of $7$ share a digit at any position. The autocorrelation lens looks at the same matrix from a different angle. It turns the diagonal-of-ones-and-off-diagonal-of-zeros pattern into a list of integers indexed by shift.

Compute the autocorrelation by hand. The repeating block of $1/7$ is $142857$, six digits long. Start with shift zero. The shift-zero entry counts the positions where the string agrees with itself, position by position, and the answer is always the cycle length. Every position agrees with itself, so the entry at shift zero is six. This is the same fact as "the diagonal of the cross-alignment matrix is all ones," now restated in the language of the autocorrelation. The shift-zero entry of $R$ and the diagonal of the matrix are two names for one trivial observation.

Now shift by one position. Slide $142857$ one place to the left and lay it under the original. $1$ versus $4$, $4$ versus $2$, $2$ versus $8$, $8$ versus $5$, $5$ versus $7$, $7$ versus $1$. Six positions, six disagreements, zero matches. The entry at shift one is zero, exactly because the off-diagonal of the matrix is zero.

Shift two, three, four, five. Each one gives the same answer for the same reason. The whole autocorrelation of $142857$ is

```
shift:    0  1  2  3  4  5
matches:  6  0  0  0  0  0
```

A single spike of size $6$ at shift zero, silence everywhere else. The simplest possible shape an autocorrelation can have. Now run a Fourier transform through this list. The Fourier transform of a delta function (a single spike followed by silence) is a constant. Every frequency receives the same weight. Every one of the six eigenvalues of the cross-alignment matrix at $p = 7$ is equal to one.

That is the spectral signature of the digit-partitioning regime. A single spike in the autocorrelation produces a flat spectrum. Every tone equally loud, no pattern standing out, no melody. The matrix is the identity. The identity sounds like white noise.

## A two-tone chord at $p = 13$

At $p = 7$ the cross-alignment matrix is the identity by default, and the spectrum is six copies of the number one. White noise. At $p = 11$ the same thing happens for the same reason. Both primes are digit-partitioning, both matrices are the simplest possible, both spectra are flat.

Then comes $p = 13$, and the program does its first interesting thing.

The base $10$ stops generating the full set of nonzero residues modulo $13$. It only generates half of them. The fractions of $13$ split into two separate groups of six, the cross-alignment matrix is no longer the identity, and you would naively expect the spectrum to spread out into a dozen scattered eigenvalues. What you find instead is that the spectrum collapses to exactly two values, $4/3$ and $2/3$, each appearing six times. Twelve eigenvalues, two distinct numbers, perfectly balanced.

Two notes. Just two. The first prime where the matrix has any structure at all produces the cleanest possible chord, and the cleanness is forced by a specific fact about how the cosets of $13$ talk to each other. Once you see the fact, the eigenvalues being *exactly* these two numbers becomes the only thing they could have been. Here is the walk.

[The cross-alignment matrix paper](https://alexpetty.com/the-cross-alignment-matrix/) lays out the two groups in detail. The first group is the rotations of $076923$. The second is the rotations of $153846$. Two distinct repeating decimals, six rotations each, twelve fractions total.

Within each group the matrix has the same trivial pattern as $p = 7$. Two distinct rotations of $076923$ never agree at any position, and two distinct rotations of $153846$ never agree at any position either. Each group on its own gives an identity-pattern $6 \times 6$ block.

The interesting part is the cross-group entries. Take $1/13 = 076923$ and walk through the second group, looking for any fraction that shares digits with it at common positions. Most of the comparisons come up empty. But against $11/13 = 846153$, two positions agree. At position three, both have $6$. At position six, both have $3$. Two matches.

Try $10/13$ against the second group. Same story. There is exactly one fraction in the second group that matches it at exactly two positions, and a complete blank against the other five. Try every fraction in the first group against the second group. Each one finds exactly one cross-group partner that matches at exactly two positions, and zero matches against everyone else.

So the cross-alignment matrix of $13$ has a specific structure. Inside each group, the identity pattern. Across groups, a sparse pattern where each fraction is paired with exactly one partner at proportion $2/6 = 1/3$, and zero everywhere else. Algebraically, the matrix is

$$\mathbf{A}(13) = \mathbf{I} + \tfrac{1}{3} \mathbf{P},$$

where $\mathbf{I}$ is the identity and $\mathbf{P}$ is the permutation matrix that swaps each fraction with its unique cross-group partner.

That permutation has a special property. If you apply it twice, you get back where you started, because swapping twice returns each fraction to itself. Permutations whose square is the identity are called *involutions*, and involutions have a very rigid spectrum. Half of their eigenvalues are $+1$ and the other half are $-1$. So the eigenvalues of $\mathbf{P}$ are six $+1$s and six $-1$s, in some basis.

Combine this with the formula above. The eigenvalues of $\mathbf{I} + (1/3) \mathbf{P}$ are obtained by adding $1$ to each eigenvalue of $(1/3) \mathbf{P}$. So the eigenvalues of the cross-alignment matrix at $p = 13$ are

$$1 + \tfrac{1}{3} = \tfrac{4}{3} \quad \text{and} \quad 1 - \tfrac{1}{3} = \tfrac{2}{3},$$

each appearing six times. Two distinct eigenvalues. Two notes. The harmonic portrait of the prime $13$ in base $10$ is a two-tone chord, $4/3$ above and $2/3$ below.

The first time you watch this happen it looks like an accident. Why $1/3$ specifically? Because the cross-group matching count is $2$ and the cycle length is $6$, and the proportion is $2/6 = 1/3$. Why is the matrix the identity plus an involution? Because the cross-group pairing happens to be a perfect matching, and a perfect matching is by definition an involution. Why does the identity-plus-an-involution structure give exactly two eigenvalues? Because that is what involutions do. Each step is forced by the previous one, and the chain ends with $4/3$ and $2/3$ as the only possible values. Looking back, you realize the spectrum had no choice.

## The three regimes

The two examples at $p = 7$ and $p = 13$ together sketch most of the taxonomy. Three regimes, three spectral shapes:

**Digit-partitioning primes.** The autocorrelation is a single spike followed by silence. Its Fourier transform is flat. Every eigenvalue equals one. The matrix is the identity, and the identity sounds like white noise. There is no preferred frequency, no chord, no melody.

**Two-coset primes.** The base $10$ generates only half the residues, the fractions split into two cosets, and the cross-coset matching makes the matrix an identity-plus-involution. The spectrum collapses to two values, $1 + m/L$ and $1 - m/L$, where $m$ is the number of cross-coset matches and $L$ is the cycle length. The field plays a two-tone chord whose interval is set by the matching count.

**Primitive-root primes (genuinely large case).** The base $10$ generates everything. The matrix is a full circulant. The eigenvalues are the harmonic content of an autocorrelation that is no longer just a delta or a perfect-matching pair. The spectrum spreads out across an interval, with multiple distinct eigenvalues at multiple distinct heights. The field plays a complex chord. The smallest base-$10$ example is $p = 17$, whose autocorrelation has nontrivial structure at several shifts, and whose nine distinct eigenvalues spread between about $0.25$ and $1.75$. The closed-form computation of those eigenvalues from the bin sizes of the digit function is the next problem I want to solve. For now, the takeaway is that this regime is where the harmonic content actually starts to be interesting.

In every regime, the spectrum is the complete invariant of the matrix's coherence geometry. The single scalars from earlier in the program ($\alpha$, $\sigma$, $F$) are averages over this spectrum. The matrix from [the cross-alignment matrix paper](https://alexpetty.com/the-cross-alignment-matrix/) is a snapshot of the spectrum in the position basis. The list of eigenvalues itself is the deeper object.

## The doorway to harmonic analysis

There is one more thing to say about the spectrum, and it is the thing I have come to think of as a doorway.

The Fourier transform used to compute the eigenvalues is a sum over the harmonics of a finite cyclic group. Each eigenvalue is the inner product of the autocorrelation function with one of those harmonics. Viewed this way, the spectrum is a *character expansion* of the autocorrelation. The eigenvalues are not just numbers attached to a matrix. They are the components of a single function (the autocorrelation) projected onto the natural basis of a finite group (the additive characters of $\mathbb{Z}/L\mathbb{Z}$).

Once you see the eigenvalues as a character expansion, you can ask the questions that harmonic analysis on finite groups knows how to answer. Which characters carry the most weight? What does the transform look like at low frequencies versus high frequencies? When does it concentrate? When does it spread? These are the questions I want to take up next, in a language the alignment program did not have until this paper.

The natural next step is to take the autocorrelation itself and ask where its closed form comes from. My current line of attack uses a classical object from Fourier analysis applied to runs of consecutive integers. If it lands, the eigenvalues become explicit functions of the bin sizes of the digit function, and the entire spectrum is computable from elementary data without ever building the matrix.

Whether or not that line of attack works, the matrix is now the bridge from counting digits to doing harmonic analysis on the field of fractions. The eigenvalues are the first thing we hear after we cross it.

## A note from 2026

*April 2026*

The character expansion identified here, that the eigenvalues of the cross-alignment matrix are inner products of the autocorrelation with the additive characters of $\mathbb{Z}/L\mathbb{Z}$, turned out to be the hinge of the alignment program. This is the paper where the program first stopped doing combinatorics on digits and started doing harmonic analysis on a finite cyclic group, and every later paper in the series uses the language born here. Whether the move is summing bin Fourier coefficients, taking cross-spectral products of bin indicators, or decomposing the collision invariant table over Dirichlet characters at conductor $b^2$, every later identity is a character expansion of one finite signed table or another. They all trace back to the observation in this paper.

The line of attack on the autocorrelation that I sketched in the closing section did land. In the immediate sequel, [The Spectral Power of the Digit Function](https://alexpetty.com/the-spectral-power-of-the-digit-function/), the additive characters got pushed all the way down to the bin level. The bin indicators turned out to have an explicit Fourier transform, the Dirichlet kernel of classical nineteenth-century harmonic analysis applied to runs of consecutive integers, and the sum of squared bin coefficients ended up encoding every magnitude-side invariant of the alignment program. The closed-form expression for the autocorrelation followed shortly after in [the autocorrelation formula](https://alexpetty.com/the-autocorrelation-formula/), and once it was in hand the eigenvalue spectrum at every prime became computable from elementary data on the bin sizes, with no need to build the matrix at all. The matrix is no longer the only path to its own eigenvalues.

Further on, the same character expansion reappears in the [collision spectrum](https://alexpetty.com/the-collision-spectrum/) as the decomposition of the collision invariant table over Dirichlet characters modulo $b^2$. The two settings differ in scope but the move is the same. Take a finite signed table on a multiplicative group, run it through the character basis, and read off the structural content as a list of inner products.

The two-coset case at $p = 13$, with its rigid involution and its two-level spectrum, is the structural ancestor of the *paired chirality* observed in the collision invariant program. There, the collision invariant table at conductor $b^2$ has a complement involution that pairs each residue with its negation, and the table's spectrum collapses onto two values whenever the involution is exact. At $p = 13$ the pairing is between cross-coset fractions; in the collision program the pairing is the complement reflection. The mechanism is the same. An exact involution forces a two-level spectrum.

.:.

---

## Try it yourself

```
$ ./nfield spectrum 7
  eigenvalues: 1, 1, 1, 1, 1, 1
  flat spectrum (digit-partitioning prime)

$ ./nfield spectrum 13
  eigenvalues: 4/3 (mult 6), 2/3 (mult 6)
  two-coset prime, two-level spectrum

$ ./nfield spectrum 17
  eigenvalues: nine distinct values in [0.25, 1.75]
  primitive-root prime, full DFT spectrum
```

At $p = 7$, every eigenvalue is one. There is nothing to see, and that nothing is the point. The autocorrelation is a delta function, its Fourier transform is constant, and the matrix is silent. At $p = 13$, the spectrum collapses to two levels because the involution structure is so rigid. The two notes $4/3$ and $2/3$ are the only sounds the prime can produce. At $p = 17$ the constraint loosens. The spectrum opens up and the prime starts to have real harmonic content, nine distinct tones spread across an interval. This is the regime where the digit function begins to do harmonic work that is not dictated by trivial structure.

The progression from $p = 7$ to $p = 13$ to $p = 17$ is the progression from silence, to a chord, to harmony. Each prime sounds more like itself than the one before.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Spectral Structure of Fractional Fields](https://github.com/alexspetty/nfield/blob/main/research/spectral_structure.pdf)

---

*Alexander S. Petty*
July 2021 (updated April 2026)
.:.
