# The Coherence Decomposition

[The Three-Tier Theorem](https://alexpetty.com/the-three-tier-theorem/) classified integers by alignment. But it left a natural question. When the alignment is high, why is it high?

The alignment compares every fraction of $n$ to $1/n$. That mixes together two different effects. Sometimes $1/n$ is genuinely unusual inside its own field. Sometimes the whole field is already internally coherent, and $1/n$ benefits from that shared structure. The alignment number does not separate those two contributions.

## Two pieces, one sum

They come apart cleanly. Define a second number, the *pairwise alignment*, written $\sigma(n)$, as the average digit-match proportion between *all* pairs of fractions, not just pairs that involve $1/n$. This measures how much the fractions agree with each other on average, regardless of which one you pick as the reference.

Now define a third number, the *focused alignment*, by

$$F(n) = \alpha(n) - \sigma(n).$$

This is the excess agreement that $1/n$ has over and above what the field already has with itself.

The two new numbers add up to the original one:

$$\alpha(n) = F(n) + \sigma(n).$$

One piece is focused on $1/n$. The other is spread across the field. The alignment is the sum.

The paper proves explicit closed forms for both pieces when $p$ is a digit-partitioning prime in the base and $n = pm$ for $m$ a smooth integer. The focused part is

$$F(pm) = \frac{m}{pm-1}$$

and the pairwise part is

$$\sigma(pm) = \frac{m-1}{pm-1}.$$
As $m$ grows, both numbers approach the same limit $1/p$, and the total alignment approaches $2/p$. At infinite resolution, the total coherence splits evenly between the focused part and the pairwise part.

## The golden gap

At $p = 3$, the focused part approaches $1/3 \approx 0.333$. The pairwise part approaches the same number. Neither one reaches the golden threshold at $0.618$. Not separately. Not even close.

But $1/3 + 1/3 = 2/3 \approx 0.667$. Above.

That is the **golden gap**. The threshold sits above each component but below their sum. The two pieces need each other to clear the line, and at $p = 3$ they have each other. At no other prime.

![The golden gap](https://alexpetty.com/content/images/2026/04/coherence_golden_gap-1.png)

The gold bar is the focused part. The blue bar is the pairwise part. At $p = 3$, the two stack together and cross the golden line. At $p = 5$, the sum is $0.4$. At $p = 7$, it is $0.286$. The bars shrink as the prime grows.

The golden ratio selected 3 in [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) by sitting between $2/3$ and $2/5$, in the gap between consecutive primes. The decomposition gives another view of the same fact. At $p = 3$, the threshold sits between the components and their sum. For every larger prime, even the total falls below the line.

## The grid

Compare every fraction of an integer to every other fraction, digit by digit. Record the proportion of matches for each pair. Lay them in a grid. At $p = 11$, the grid tells the whole story.

```
$ ./nfield field 11
   1/11 => 0.|09|      6/11 => 0.|54|
   2/11 => 0.|18|      7/11 => 0.|63|
   3/11 => 0.|27|      8/11 => 0.|72|
   4/11 => 0.|36|      9/11 => 0.|81|
   5/11 => 0.|45|     10/11 => 0.|90|
```

Ten fractions. Ten distinct two-digit blocks. No two share a digit at any position. So the grid has a one everywhere a fraction meets itself and a zero everywhere it meets a stranger.

```
        1/11 2/11 3/11 4/11 5/11 6/11 7/11 8/11 9/11 10/11
 1/11 [  [1]   0    0    0    0    0    0    0    0    0  ]
 2/11 [   0   [1]   0    0    0    0    0    0    0    0  ]
 3/11 [   0    0   [1]   0    0    0    0    0    0    0  ]
 4/11 [   0    0    0   [1]   0    0    0    0    0    0  ]
 5/11 [   0    0    0    0   [1]   0    0    0    0    0  ]
 6/11 [   0    0    0    0    0   [1]   0    0    0    0  ]
 7/11 [   0    0    0    0    0    0   [1]   0    0    0  ]
 8/11 [   0    0    0    0    0    0    0   [1]   0    0  ]
 9/11 [   0    0    0    0    0    0    0    0   [1]   0  ]
10/11 [   0    0    0    0    0    0    0    0    0   [1] ]
```

The pairwise part $\sigma$ is zero. No fraction agrees with any other. The cross-alignment matrix of $11$ is the identity.

Now take $p = 13$. Twelve fractions, six-digit repeating blocks.

```
$ ./nfield field 13
   1/13 => 0.|076923|      7/13 => 0.|538461|
   2/13 => 0.|153846|      8/13 => 0.|615384|
   3/13 => 0.|230769|      9/13 => 0.|692307|
   4/13 => 0.|307692|     10/13 => 0.|769230|
   5/13 => 0.|384615|     11/13 => 0.|846153|
   6/13 => 0.|461538|     12/13 => 0.|923076|
```

Build the grid the same way. Dots are zeros.

```
          1    2    3    4    5    6    7    8    9   10   11   12
   1  [  [1]   .    .    .    .    .    .    .    .    .  0.3    . ]
   2  [   .   [1]   .    .    .    .    .    .    .    .    .  0.3 ]
   3  [   .    .   [1]   .    .    .  0.3    .    .    .    .    . ]
   4  [   .    .    .   [1] 0.3    .    .    .    .    .    .    . ]
   5  [   .    .    .  0.3  [1]   .    .    .    .    .    .    . ]
   6  [   .    .    .    .    .   [1]   .    .    .  0.3    .    . ]
   7  [   .    .  0.3    .    .    .   [1]   .    .    .    .    . ]
   8  [   .    .    .    .    .    .    .   [1] 0.3    .    .    . ]
   9  [   .    .    .    .    .    .    .  0.3  [1]   .    .    . ]
  10  [   .    .    .    .    .  0.3    .    .    .   [1]   .    . ]
  11  [ 0.3    .    .    .    .    .    .    .    .    .   [1]   . ]
  12  [   .  0.3    .    .    .    .    .    .    .    .    .   [1]]
```

Six pairs of fractions share digits at some positions. The $0.3$ entries are small, but they are there. That is the pairwise part. Average any row including the diagonal and you get $\alpha$. Average the off-diagonal entries and you get $\sigma$.

At $p = 11$, there are no off-diagonal matches. At $p = 13$, they begin to appear.

Scale up.

![Grid progression](https://alexpetty.com/content/images/2026/04/coherence_grid_progression-4.png)

Twenty primes, from 3 to 151. At $p = 3$, the grid is nearly full. At $p = 5$, completely full. At $p = 7$ and $p = 11$, the grid goes dark: white diagonal, black everywhere else. These are the digit-partitioning primes, with $\sigma = 0$. Then at $p = 13$, the first off-diagonal entries appear and the filling begins.

More off-diagonal agreement does not mean higher alignment. The pairwise part can grow while the focused part shrinks.

## The pinch

The golden gap has a simple algebraic form. The condition for $1/\varphi$ to sit inside the gap is

$$\frac{1}{p} < \frac{1}{\varphi} < \frac{2}{p}.$$

The left inequality says $p > \varphi \approx 1.618$. Every prime satisfies that. The right one says $p < 2\varphi \approx 3.236$. Only two primes satisfy that, $p = 2$ and $p = 3$. The prime 2 is degenerate, so among odd primes only $p = 3$ remains.

![The pinch](https://alexpetty.com/content/images/2026/04/coherence_golden_pinch-1.png)

Each bar is the interval from $1/p$ to $2/p$ for one prime. The golden line at $1/\varphi$ cuts through only one of them. Only the bar for $p = 3$ reaches across the line, with $1/3$ on one side and $2/3$ on the other.

The golden ratio is not in this picture for aesthetic reasons. It is the unique number whose reciprocal fits between $1/p$ and $2/p$ at exactly one odd prime.

The threshold is crossed not by one dominant piece, but by two smaller pieces whose sum succeeds only at a single prime.
## A note from 2026

*April 2026*

This paper is easier to appreciate after [The Cross-Alignment Matrix](https://alexpetty.com/the-cross-alignment-matrix/). The grid that appears here as a computational tool becomes the real object there. Seen from that angle, the split into focused and pairwise parts is already asking a structural question: how much of the alignment belongs to $1/n$ itself, and how much belongs to the field around it?

That way of splitting a quantity into a distinguished part and a background part shows up again in [The Collision Transform](https://alexpetty.com/the-collision-transform/), where the global mean is removed before the Fourier analysis begins. The language is different, but the instinct is the same.

The exceptional role of the prime $3$ also survives the transition. Here $3$ is the only prime for which the two pieces can add up across the golden line. In [The Collision Spectrum](https://alexpetty.com/the-collision-spectrum/), the same prime becomes exceptional again from a different direction. The agreement is too clean to feel accidental.

One point remains especially satisfying. The pairwise term $\sigma$ vanishes exactly at the digit-partitioning primes. The dark grids at $p=7$ and $p=11$ are not just visually simple; they are the places where the background coherence drops all the way to zero.

.:.

---

## Try it yourself

Pull the alignment apart and see what each piece is doing.

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

Watch what happens as the smooth part grows. The focused number $F$ drops from $0.364$ toward the limit $1/3$. The pairwise number $\sigma$ rises from $0.273$ toward the same limit. The two components move toward each other while their sum stays above $1/\varphi$.

Now try $7$. No collisions, no shared digits.

```
$ ./nfield decompose 7
  alpha  = 0.167  (total)
  sigma  = 0.000  (background)
  F      = 0.167  (focused)
  1/phi in gap = no
```

Zero pairwise background. The fractions of $7$ are completely independent. The matrix is the identity. The only coherence is focused, and $1/7$ alone cannot carry the total anywhere near $0.618$.

Now $77 = 7 \times 11$. Two primes that individually had zero pairwise part.

```
$ ./nfield decompose 77
  alpha  = 0.088  (total)
  sigma  = 0.065  (background)
  F      = 0.022  (focused)
  1/phi in gap = no
```

Both components are present but both are tiny. Together they reach $0.088$.

The decomposition is not just bookkeeping. It tells you why an integer fails to make the cut. At digit-partitioning primes like $7$ and $11$, the pairwise part vanishes. At composite Tier 3 numbers like $77$, both components are present but small. At Tier 2, both are needed. At Tier 1, the alignment is trivially perfect.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Coherence Decomposition](https://github.com/alexspetty/nfield/blob/main/research/coherence_decomposition.pdf)

---

*Alexander S. Petty*
January 2021 (updated April 2026)
.:.
