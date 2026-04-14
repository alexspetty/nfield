# The Coherence Decomposition

Walk into a room where everyone is singing the same note. Now one person sings louder. Is that person leading, or just singing along?

That is the question this post asks about the fractions of an integer.

## Signal and background

[The Three-Tier Theorem](https://alexpetty.com/the-three-tier-theorem/) classified every integer by its alignment. The golden line sorts them cleanly. But it left a question I could not shake. When the alignment is high, WHY is it high?

The alignment measures how often the fractions of $n$ agree with $1/n$ at the same digit position. But when the alignment is high, is it high because $1/n$ is special, or because the fractions already agreed with each other and $1/n$ is just one of them? In a field where every fraction shares digits with every other, matching $1/n$ is not an achievement. It is conformity. In a field where the fractions are independent, matching $1/n$ means something. The alignment number cannot tell you which situation you are in. It conflates the signal with the background.

I wanted to pull them apart.

## Two pieces, one sum

They come apart cleanly. Define a second number, the *pairwise alignment*, written $\sigma(n)$, as the average digit-match proportion between *all* pairs of fractions, not just pairs that involve $1/n$. The pairwise alignment measures the background hum of the field. It says how much the fractions agree with each other on average, regardless of which one you pick as the reference. It is a property of the field as a whole, not of any chosen member.

Now define a third number, the *focused alignment*, by

$$F(n) = \alpha(n) - \sigma(n).$$

This is the excess agreement that $1/n$ has over and above what every fraction has with every other. It is how much $1/n$ stands out from the crowd. It is the part of the total alignment that genuinely belongs to $1/n$, not to the field's own internal harmony.

The two new numbers add up to the original one,

$$\alpha(n) = F(n) + \sigma(n).$$

Two pieces. One is the focused signal, the other is the diffuse background. Both are computable from the field alone, with no need to single out any fraction in advance. The alignment is the sum.

The paper proves explicit closed forms for both pieces when $p$ is a digit-partitioning prime in the base and $n = pm$ for $m$ a smooth integer. The focused part is $F(pm) = m/(pm - 1)$. The pairwise part is $\sigma(pm) = (m - 1)/(pm - 1)$. As $m$ grows large, both numbers approach the same limit $1/p$, and the total alignment approaches $2/p$. So at infinite resolution, the total coherence of the field splits exactly in half. One half is focused on $1/n$. One half is diffuse across the whole field. Equal contributions. A clean symmetry hiding inside the alignment formula all along.

## The golden gap

Here is where the story turns.

At $p = 3$, the focused signal approaches $1/3$. That is $0.333$. The golden threshold is $0.618$. The signal alone falls short by a wide margin.

The background hum also approaches $1/3$. Same number. Same shortfall. The hum alone falls just as short.

So neither the signal nor the background can reach the golden line. Not separately. Not by a little. Not even close.

Add them.

$1/3 + 1/3 = 2/3 \approx 0.667$.

Above.

That is the **golden gap**. The threshold sits above each component but below their sum. The focused signal is too weak. The background hum is too quiet. But the two together clear the line. They need each other. At $p = 3$, they have each other. At $p = 3$ and nowhere else.

![The golden gap](https://alexpetty.com/content/images/2026/04/coherence_golden_gap-1.png)

The gold bar is the focused signal. The blue bar is the background hum. At $p = 3$, the two stack together and cross the golden line. At $p = 5$, the sum is $0.4$. At $p = 7$, $0.286$. The bars shrink and the line recedes. The cooperation that works at 3 fails everywhere else, and it fails by a wider margin at every successive prime.

The golden ratio selected 3 in [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) by sitting between $2/3$ and $2/5$, in the gap between consecutive primes. That was selection by exclusion. The decomposition reveals something sharper. At $p = 3$, the golden threshold sits between the *components* of alignment and their sum. It is not just that no other prime's total reaches the line. It is that no other prime's components are configured to cooperate. The signal and the background are balanced at $p = 3$ in a way they are balanced at no other prime. The gap is not between primes. It is inside the prime itself.

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

A room full of strangers. Every fraction recognizes only itself. The background is silent. This is the **cross-alignment matrix** of $11$, and it is the identity matrix, the simplest a matrix of its size can be.

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

Six pairs of fractions have started recognizing each other. The 0.3 entries are faint, but they are there. The room has a hum.

That hum is $\sigma$. Read any single row and average it, diagonal included, and you get $\alpha$. Ignore the diagonal and average everything else, and you get $\sigma$. The decomposition $\alpha = F + \sigma$ is just the question: how much of this grid lights up when you take away the fraction's agreement with itself?

At $p = 11$, nothing lights up. The grid is dark off the diagonal. No hum.

At $p = 13$, twelve faint points glow, in six symmetric pairs. A little hum.

Now scale up and watch it happen.

![The room fills up](https://alexpetty.com/content/images/2026/04/coherence_grid_progression-4.png)

Twenty primes, from 3 to 151. At $p = 3$, the grid is nearly full. At $p = 5$, completely full; all four fractions agree everywhere. At $p = 7$ and $p = 11$, the grid goes dark. White diagonal, black everywhere else. These are the digit-partitioning primes. No hum at all. Then at $p = 13$, the first blue appears off the diagonal and the filling begins. By $p = 19$, nearly half. By $p = 29$, two thirds. By $p = 97$, the diagonal is a thin white thread in a sea of blue. By $p = 151$, you can barely find it.

The white diagonal is the signal, each fraction's agreement with itself. Everything else is the background, $\sigma$, the hum of the field agreeing with itself. As the prime grows, the hum gets louder. More fractions, more collisions, more shared digits, more light in the grid.

But louder does not mean higher. At $p = 97$, the grid is 91% lit and the alignment is $0.020$. The background is deafening and the total is tiny. The fractions agree with each other everywhere, but none of them agrees with $1/n$ much at all. The glow is broad and flat. No concentration. No structure. At $p = 3$, the grid is small and the glow concentrates where it matters. The golden gap is visible in the grids. It is the difference between concentrated light and diffuse light.

## The pinch

The golden gap has an algebraic skeleton. The condition for $1/\varphi$ to sit inside the gap is

$$\frac{1}{p} < \frac{1}{\varphi} < \frac{2}{p}.$$

Two inequalities. The left one says $p > \varphi \approx 1.618$. Every prime satisfies that. The right one says $p < 2\varphi \approx 3.236$. Only two primes satisfy that, $p = 2$ and $p = 3$. The prime 2 is degenerate; every even smooth denominator already has alignment 1. So among odd primes, $p = 3$ is the only one.

![The pinch](https://alexpetty.com/content/images/2026/04/coherence_golden_pinch-1.png)

Each bar is the interval from $1/p$ to $2/p$ for one prime. The golden line at $1/\varphi$ cuts through only one of them. At $p = 5$, the interval already sits entirely below the line. At $p = 7$, further below. At $p = 23$, the interval is a sliver near zero. The bars shrink and recede as the primes grow. Only the bar for $p = 3$ reaches across the golden line, with $1/3$ on one side and $2/3$ on the other.

The golden ratio is not in this picture for aesthetic reasons. It is the unique number whose reciprocal fits between $1/p$ and $2/p$ at exactly one prime.

## A note from 2026

*April 2026*

The grid in this post became a real object. [The Cross-Alignment Matrix](https://alexpetty.com/the-cross-alignment-matrix/) gave it a name and a formal structure. The [collision invariant](https://alexpetty.com/the-collision-invariant/) replaced the signal (digit matches between fractions) with a sharper one (collision counts under multiplication) but kept the same grid, the same complement involution, the same antisymmetry. The room changed. The architecture did not.

Splitting alignment into signal and background turned out to be the same move the rest of the program would make at every scale. The [collision transform](https://alexpetty.com/the-collision-transform/) subtracts the global mean of $-1/2$ before taking the Fourier transform. That is the same split. The background hum of this post is the trivial-character contribution. The focused signal is everything else. Different vocabulary, same decomposition.

The golden gap appeared again, from a completely different direction. In the [collision spectrum](https://alexpetty.com/the-collision-spectrum/), the prime 3 admits a closed-form null cocycle at its boundary alphabet that no other prime in the family admits. The alignment decomposition selects $p = 3$ from one side. The boundary algebra selects it from the other. Two routes, one prime. This is not a coincidence. It is the same structural fact, refracted through two different instruments.

One small confirmation that still satisfies me. The background $\sigma$ vanishes if and only if the prime is digit-partitioning. The dark grids at $p = 7$ and $p = 11$ in the progression panel are exactly the primes where the [digit-partitioning](https://alexpetty.com/digit-partitioning-primes-and-the-alignment-formula/) condition holds. Two characterizations, two angles, same object. That is how you know the framework is right.

.:.

---

## Try it yourself

Pull the alignment apart and see which piece carries the weight.

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

Watch what happens as the smooth part grows. The focused number $F$ drops from $0.364$ toward the limit $1/3$. The background number $\sigma$ rises from $0.273$ toward the same limit. The two components converge toward each other. The focused signal weakens, the background strengthens, but their sum holds above $1/\varphi$ the entire time. The two pieces trade weight, and the golden threshold stays below them.

Now try $7$. No collisions, no shared digits, no hum.

```
$ ./nfield decompose 7
  alpha  = 0.167  (total)
  sigma  = 0.000  (background)
  F      = 0.167  (focused)
  1/phi in gap = no
```

Zero background. The fractions of $7$ are completely independent. The matrix is the identity. There is no hum. The only coherence is focused, and $1/7$ alone cannot carry the total anywhere near $0.618$.

Now $77 = 7 \times 11$. Two primes that individually had no hum at all.

```
$ ./nfield decompose 77
  alpha  = 0.088  (total)
  sigma  = 0.065  (background)
  F      = 0.022  (focused)
  1/phi in gap = no
```

Both components are present but both are tiny. The focused signal is nearly gone, since $1/77$ barely stands out from its own field. The background exists but is faint. Together they reach $0.088$. The golden threshold is seven times higher.

The decomposition is not just bookkeeping. It tells you *why* an integer fails to make the cut. At Tier 3 primes like $7$ and $11$, the failure is total background absence. At composite Tier 3 numbers like $77$, the failure is total signal weakness. At Tier 2 (the golden family), the success is the cooperation of both. At Tier 1 (smooth), $\sigma = 1$ by trivial conformity. Each tier has its own coherence signature, and the decomposition gives them a common language.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Coherence Decomposition](https://github.com/alexspetty/nfield/blob/main/research/coherence_decomposition.pdf)

---

*Alexander S. Petty*
January 2021 (updated April 2026)
.:.
