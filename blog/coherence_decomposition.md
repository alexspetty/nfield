# The Coherence Decomposition

Walk into a room where everyone is singing the same note. Now one person sings louder. Is that person leading, or just singing along?

That is the question this paper asks about the fractional field. The alignment $\alpha(n)$ measures how well the whole field matches $1/n$. But how much of that match is because $1/n$ is special, and how much is because the fractions already agree with each other, and $1/n$ is just one of them?

In a field where every fraction shares digits with every other fraction, matching $1/n$ is not an achievement. It is conformity. In a field where fractions are independent, matching $1/n$ means something. The alignment number cannot tell you which situation you are in. It conflates the signal with the background.

I wanted to pull them apart.

## The decomposition

They come apart cleanly:

$$\alpha = F + \sigma$$

Two terms. The first, $\sigma(n)$, is the *pairwise alignment*: the average digit-match proportion between all pairs of fractions, not just pairs that involve $1/n$. It measures the background hum of the field. How much do the fractions agree with each other, regardless of which one you pick as the reference?

The second, $F(n) = \alpha - \sigma$, is the *focused alignment*: the excess. How much does $1/n$ stand out from the crowd? How much of the total coherence belongs to $1/n$ specifically, rather than to the field's own internal harmony?

Two new invariants of the fractional field. Both computable from the field alone, no choice of distinguished member required.

For digit-partitioning primes $p$ and smooth $m$, both have closed forms:

$$F(pm) = \frac{m}{pm-1}, \qquad \sigma(pm) = \frac{m-1}{pm-1}$$

And as $m$ grows, both limits land on the same number:

$$F \to 1/p, \qquad \sigma \to 1/p, \qquad \alpha \to 2/p$$

At infinite resolution, the total coherence splits exactly in half. One part focused on $1/n$. One part diffuse across the whole field. Equal contributions. A clean symmetry hiding inside the alignment formula all along.

## The golden gap

Now look at where $1/\varphi$ falls.

At $p = 3$, the focused limit is $1/3 \approx 0.333$. Below the golden threshold. The background limit is also $1/3$. Also below. Neither part, on its own, reaches $1/\varphi \approx 0.618$.

But together: $1/3 + 1/3 = 2/3 \approx 0.667$. Above.

This is the **golden gap**. The threshold sits between the individual contributions and their sum. The focused alignment cannot reach it. The diffuse alignment cannot reach it. But the two together, the specific agreement with $1/n$ and the general agreement of the field with itself, combine to cross the line.

Among primes $p \geq 3$, only $p = 3$ has this property. At $p = 5$, the total limit is $2/5 = 0.4$. Both contributions could be as large as they like, and the total would still fall short. The window between $F$ and $\alpha$ has closed: there is no room for $1/\varphi$ to fit inside it.

The three-tier theorem is this gap made structural. At $p = 3$, the background hum of the field is just loud enough to carry the focused signal above the threshold. At every other prime, the hum is too quiet or the signal is too weak. The golden ratio sits in the one place where both contributions are needed and both are sufficient.

This is a sharper version of "the golden ratio selects the prime three." The earlier framing said the threshold sits between the alignment limits of consecutive primes ($2/3$ and $2/5$), and there is no prime in the gap, so 3 is special by exclusion. The decomposition framing says: at the prime 3, the threshold sits between *the components of alignment itself*, and the configuration is unique to that prime. Same selection, sharper mechanism.

## The matrix

There is a way to see all of this at once. Take the field of 7:

```
1/7 => 0.|142857|
2/7 => 0.|285714|
3/7 => 0.|428571|
4/7 => 0.|571428|
5/7 => 0.|714285|
6/7 => 0.|857142|
```

Compare 1/7 and 2/7, digit by digit. Position 1: 1 vs 2. Different. Position 2: 4 vs 8. Different. Position 3: 2 vs 5. Different. Every position, every pair, zero matches. Now do this for all six fractions against all six fractions. You get a 6 x 6 grid. The entry in row $k$, column $j$ is the fraction of positions where $k/7$ and $j/7$ share the same digit.

That grid is the **cross-alignment matrix** $\mathbf{A}(7)$. At the prime 7, it is the identity matrix: ones on the diagonal (every fraction matches itself), zeros everywhere else. The fractions are strangers. There is no background coherence. The room is silent until $1/n$ starts singing.

At larger primes, the matrix is no longer the identity. Take $p = 13$. Twelve fractions, but now some pairs share digits at certain positions. The off-diagonal entries are no longer all zero. The matrix develops structure: fractions in the same coset show higher agreement, fractions in different cosets show less. Bands appear. Blocks form.

The matrix encodes the full coherence geometry of the field. The diagonal carries the identity of each fraction. The off-diagonal carries the background. The alignment $\alpha(n)$ is the average of the entire row corresponding to $1/n$: the diagonal entry (which is 1) plus all the off-diagonal entries in that row. The pairwise alignment $\sigma(n)$ is the average of all the off-diagonal entries of the matrix, taken over every pair. The decomposition $\alpha = F + \sigma$ is not an abstraction. It is a statement about which part of the matrix you are reading.

What the paper proves, for digit-partitioning primes, is that this matrix has exact closed-form structure: the non-terminating fractions partition into $p - 1$ same-repetend groups, with $m$ fractions in each group at $n = pm$. Within a group, every pair has alignment 1 (identical repetends). Across groups, every pair has alignment 0 (cyclic shifts of the same string, sharing no positions, by the digit-partitioning property). The matrix is a block matrix with $p - 1$ blocks of all 1s on the diagonal, with all 0s elsewhere among the non-terminating fractions, plus a small contribution from the terminating fractions.

The closed-form formulas for $F$ and $\sigma$ follow directly. And the golden gap, the fact that $1/\varphi$ sits between $F$ and $\alpha$ only at $p = 3$, is visible in the matrix as the unique prime where the off-diagonal blocks are exactly the right size to lift the row average above the threshold.

## Why it had to be the prime three

There is one more way to see why only $p = 3$ has the gap. It comes from the algebra.

The condition "$1/\varphi$ lies in the gap between $F$ and $\alpha$" means $F < 1/\varphi < \alpha$. With $F = \sigma$ in the limit (both equal $1/p$), this becomes:

$$\frac{1}{p} < \frac{1}{\varphi} < \frac{2}{p}$$

The left inequality says $p > \varphi \approx 1.618$, which holds for every prime. The right inequality says $p < 2\varphi \approx 3.236$, which holds only for $p = 2$ and $p = 3$. The case $p = 2$ is degenerate (every even smooth denominator gives $\alpha = 1$ trivially). So among primes $p \geq 3$, the only solution is $p = 3$.

The two inequalities pinch the prime from above and below. $1/\varphi$ is exactly the number that fits between $1/p$ and $2/p$ for $p = 3$ and no other prime. The golden ratio is not aesthetic. It is the unique threshold whose reciprocal lives in the open interval $(1/p, 2/p)$ at exactly one prime.

## Try it yourself

The `decompose` command pulls the alignment apart. Start with the golden family:

```
$ ./nfield decompose 12
  alpha  = 0.636  (total)
  sigma  = 0.273  (background)
  F      = 0.364  (focused)
  1/phi in gap = yes

$ ./nfield decompose 120
  alpha  = 0.664  (total)
  sigma  = 0.328  (background)
  F      = 0.336  (focused)
  1/phi in gap = yes
```

Look at what happens as $m$ grows. $F$ drops from 0.364 toward $1/3$. $\sigma$ rises from 0.273 toward $1/3$. They converge toward each other. The focused signal weakens. The background strengthens. But their sum holds above $1/\varphi$ the entire time. The two components trade weight, and the golden threshold stays below them.

Now the prime 7, a digit-partitioning prime in Tier 3:

```
$ ./nfield decompose 7
  alpha  = 0.167  (total)
  sigma  = 0.000  (background)
  F      = 0.167  (focused)
  1/phi in gap = no
```

Zero background. The fractions of 7 are completely independent. The matrix is the identity. There is no hum. The only coherence is focused, and $1/7$ alone cannot carry the total anywhere near 0.618.

Now a composite, $n = 77 = 7 \times 11$:

```
$ ./nfield decompose 77
  alpha  = 0.088  (total)
  sigma  = 0.065  (background)
  F      = 0.022  (focused)
  1/phi in gap = no
```

Both components are present but both are tiny. The focused signal is nearly gone: $1/77$ barely stands out from its own field. The background exists but is faint. Together they reach 0.088. The golden threshold is seven times higher.

The decomposition is not just bookkeeping. It tells you *why* an integer fails to make the cut. At Tier 3 primes like 7 and 11, the failure is total background absence. At composite Tier 3 numbers like 77, the failure is total signal weakness. At Tier 2 (the golden family), the success is the cooperation of both. At Tier 1 (smooth), $\sigma = 1$ by trivial conformity. Each tier has its own coherence signature.

---

## A note from 2026

*April 2026*

The cross-alignment matrix introduced in this post became the structural prequel to the boundary alphabet of the recent collision invariant program. The same finite signed table on the same multiplicative group, with the same complement involution, indexed by the same residue classes; only the signal is different. Where the alignment matrix records digit matches between fractions, the boundary alphabet of the [collision invariant](https://alexpetty.com/the-collision-invariant/) records the collision count of the digit function under multiplication. Both are matrices on the units of $\mathbb{Z}/n\mathbb{Z}$. Both have antisymmetric structure under the complement. Both unify into one object whose decomposition is the central content of the program.

The decomposition $\alpha = F + \sigma$ prefigured the centered/decentered split that appears in the [collision transform](https://alexpetty.com/the-collision-transform/). There, the trivial-character coefficient of the Fourier transform is exactly $-1/2$ (the global mean of the collision invariant table), and the centered invariant $S^\circ$ subtracts this constant before taking the Fourier transform. The "background hum" of the coherence post is the principal-character contribution; the "focused signal" is what remains after subtracting it. The vocabulary changed but the move is the same: separate the constant baseline from the structured part, then study each separately.

The golden gap framing, that the threshold sits between the components of alignment at exactly one prime, became one piece of a larger structural picture. In the [collision spectrum](https://alexpetty.com/the-collision-spectrum/), the prime 3 plays a privileged role for a different but related reason: at conductor 3, the boundary alphabet of the digit function admits a closed-form null cocycle that does not exist at other primes in the same family. The selection of $p = 3$ that this post derives from the alignment-decomposition algebra reappears in the recent work as the selection of $p = 3$ from the boundary-alphabet algebra. Two routes, one prime.

The pairwise alignment $\sigma$ defined here also has a clean characterization, proved in the paper as a separate proposition: $\sigma(p) = 0$ if and only if $p$ is a digit-partitioning prime. This is the same characterization the [digit-partitioning paper](https://alexpetty.com/digit-partition-primes/) gave from the digit function's injectivity, now visible from a different angle: at digit-partitioning primes, the cross-alignment matrix is the identity, so the background pairwise alignment vanishes. The two characterizations are equivalent. This is the kind of small but satisfying confirmation that happens when the framework is right: the same object becomes visible from multiple angles.

The closing question of the digit-partitioning post, what does the prime look like when you stop choosing bases and look at it directly, is answered partially here (by the cross-alignment matrix as the base-relative structural object) and completely in the recent program (where the boundary alphabet at conductor $b^2$ encodes the same information as a finite signed table on the multiplicative group).

.:.

---

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Coherence Decomposition](https://github.com/alexspetty/nfield/blob/main/research/coherence_decomposition.pdf)

*Alexander S. Petty*
June 2022 (updated April 2026)
.:.

---

**Figure prompt:**

Use the same art style as the previous images in this series (abstract mathematical visualizations, dark background, luminous geometric forms, cool blues and whites, high contrast, clean and minimal). The subject matter should be specific to this paper, not a repeat of previous images.

A single luminous form rises from a basin, splitting into two components: a sharp bright vertical beam (the focused component) and a soft diffuse glow spreading outward (the diffuse component). The two form a cross of light. A thin horizontal golden line crosses the composition. The combined light reaches above the golden line.

No text, no axes, no labels. The mathematics is in the light.

Aspect ratio: 1200 x 800 (landscape). High contrast.

**Caption:** The focused beam and the diffuse glow. Total coherence is the sum of both. For one prime, the glow carries the total above the golden line. For all others, it falls short.
