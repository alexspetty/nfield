# The Collision Fluctuation Sum

I added up the collision deviations for the first hundred primes past ten. The total came out negative.

I added up the first thousand. Still negative, and larger.

I added up the first ten thousand. Larger still.

The deviations were not cancelling. They were accumulating, slowly but steadily, in the negative direction. The more primes I added, the further the total drifted from zero.

Each prime has a [collision count](https://alexpetty.com/silent-primes/), the number of digit positions where its repetend matches a shifted copy of itself. That count sits close to its expected value of roughly $p/10$. The difference between the actual count and the expected value is a small signed number, sometimes positive, sometimes negative, sometimes zero. Add up a thousand of these small differences and you would expect the positives to cancel the negatives. The total should hover near zero. That is what random fluctuations do.

These fluctuations were not doing it. The sum was drifting, and the drift had a shape.

## The drift

The rate is $\log \log x$, the iterated logarithm. I described this function in the [character structure paper](https://alexpetty.com/the-character-structure-of-the-collision-fluctuation/). It is the slowest-growing function in ordinary analysis. Between a million and a trillion, it increases by less than one. You have to walk through truly enormous stretches of primes to see it move at all.

Here is what the accumulation looks like when I compute it across all primes up to ten million in base ten at lag one:

```
primes scanned      largest prime       accumulated sum     sum / log log p
--------------      -------------       ---------------     ---------------
     1,000              7,951              -1.37               -0.623
    10,000            104,779              -1.60               -0.652
   100,000          1,299,811              -1.77               -0.671
   664,574          9,999,991              -1.90               -0.682
```

Reading the table. The third column is the fluctuation sum, drifting slowly downward. The fourth column divides the sum by $\log \log p$, asking whether the drift is proportional to the iterated logarithm. If it is, the fourth column should settle toward a constant. It does. The ratio drifts toward $0.68$, slowing down as it climbs.

The collision fluctuation grows at the Mertens rate, the same rate at which the classical prime harmonic series $\sum 1/p$ diverges. The name "Mertens rate" comes from Franz Mertens, who proved in 1874 that $\sum_{p \le x} 1/p = \log \log x + M + o(1)$ where $M$ is a specific constant. The collision fluctuation sum grows at the same shape. The digit function's deviations accumulate with the same weight as the primes themselves.

## Every collision comes in pairs

Before I go further, there is a structural fact about the collision count that I did not expect and that constrains everything that follows.

The collision count is always even.

At every prime. For every multiplier. In every base. The count is always $0$, or $2$, or $4$, or $6$. It is never $1$, never $3$, never $5$, never $7$. Always even. No exceptions.

The proof is short and I want to show it to you, because it is one of those proofs that are as satisfying as the result.

Take a prime $p$ and a multiplier $g$. Suppose a residue $r$ is a collision, meaning $r$ and $gr$ have the same leading digit. Now look at the *complement* of $r$, which is $p - r$. This is a different residue (since $p$ is odd and greater than $2$, the residue $r$ is never equal to $p - r$). The complement map sends digit $d$ to digit $b - 1 - d$: the leading digit of $(p - r)/p$ is the nines-complement of the leading digit of $r/p$. Multiplication by $g$ does the same thing to $p - r$ that it did to $r$, because multiplication commutes with the complement map (both are linear operations on the residues). So if $r$ and $gr$ have the same leading digit, then $p - r$ and $g(p-r)$ also have the same leading digit.

Every collision has a partner. The collision at $r$ is paired with the collision at $p - r$. The two are always different residues. So the collisions come in pairs, and the total count is even.

I call this the *bilateral parity theorem*. It is a hard structural constraint. It forces the collision count $C(g)$ to be even, forces the integer $S = C - Q$ (the collision count minus the bin size) to share the parity of $Q$, and runs through every later piece of the program like a load-bearing beam.

## The four families

The persistent downward drift of the fluctuation sum is not the same at every prime. Primes in different spectral families (sorted by their last digit in base $b$) carry different biases.

In base ten there are four families: primes ending in $1$, $3$, $7$, and $9$. Each family has its own per-family average deviation. Here are those averages, computed across all primes up to ten million:

```
last digit     mean deviation
----------     --------------
    1              -1.70
    3              -1.11
    7              -0.68
    9              -0.12
```

All four are negative. That is why the sum drifts downward. But the biases are not the same.

![Per-family collision bias](https://alexpetty.com/content/images/2026/04/collision_family_biases.png)

And then a number I had not expected to see again.

Look at the family of primes ending in $7$. Its mean deviation is $-0.68$. Round that to two digits and you get $-0.67$, which is $-2/3$.

The constant $2/3$.

The same $2/3$ that appeared in [the golden ratio selects prime three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) as the alignment limit of the prime $3$, the threshold the golden ratio selected through the factorization of a self-referential cubic. The constant from the first paper in this sequence. It shows up here, in a completely different context, as the per-family collision bias of the digit-$7$ family.

I did not put it there. I did not expect it. The digit function computed it, and the golden ratio's constant was sitting inside the answer.

## The centering

So the sum drifts. Here it is again, all four cutoffs, growing and not stopping:

```
primes          raw sum
------          -------
  1,000          -1.37
 10,000          -1.60
100,000          -1.77
664,574          -1.90   ← still going
```

A divergent sum is a divergent sum, and there is nothing to do with one except watch it grow. Or so you might think.

But the drift has structure. Here is the same sum computed at different exponents in the weighting. Instead of dividing each deviation by $p$ (the exponent $s = 1$), try dividing by $p^{1.2}$ or $p^{1.5}$ (which gives large primes less weight) or by $p^{0.9}$ or $p^{0.5}$ (which gives large primes more weight):

```
primes     s = 1.5     s = 1.2     s = 1.0     s = 0.9     s = 0.5
------     -------     -------     -------     -------     -------
  100       -0.17       -0.47       -1.07       -1.42       -6.97
  500       -0.18       -0.55       -1.28       -2.02      -17.0
 1000       -0.18       -0.56       -1.37       -2.17      -21.4
 2000       -0.18       -0.57       -1.45       -2.30      -26.0
```

Look at the columns. At $s = 1.5$ and $s = 1.2$, the values stabilize. The sum converges. At $s = 1.0$, the values drift slowly (the Mertens rate). At $s = 0.9$ and $s = 0.5$, the values run away. The boundary between *settling down* and *running away* sits at exactly $s = 1$.

![The collision fluctuation sum at three exponents](https://alexpetty.com/content/images/2026/04/collision_fluctuation_boundary.png)

Now look at the per-family biases one more time:

```
last digit     mean deviation
----------     --------------
    1              -1.70
    3              -1.11
    7              -0.68
    9              -0.12
```

Every family pulls the sum downward, but by different amounts. And those amounts are *predictable*. They depend only on the prime's last digit. You do not need the collision count to know them. You do not need the repetend, or the bin size, or the multiplier. You just need to know which of the four families the prime belongs to, and that tells you the bias.

So try something. At each prime, instead of adding the raw deviation to the running total, subtract the per-family average first and add only the remainder. Keep only the part that is genuinely about the individual prime, the part you could not have predicted from the last digit alone.

Here is the operation for one prime from each family:

```
prime    last digit    raw deviation    family bias    centered
-----    ----------    -------------    -----------    --------
  101         1            -1.7            -1.70         0.0
  503         3            -2.3            -1.11        -1.2
   97         7            -3.6            -0.68        -2.9
  409         9            +0.5            -0.12        +0.6
```

Reading across each row. Start with the raw deviation (the prime's collision count minus its expected value). Subtract the family bias (the per-family average from the table above). The result, in the last column, is the *centered deviation*, the part of the wobble that is specific to this prime and not shared by its family.

The centered deviations are smaller. Some are positive, some are negative, some are near zero. They no longer all pull in the same direction. That is the difference. The raw deviations are systematically negative (every family has a negative bias). The centered deviations are mixed.

That immediately suggests the next move. If the entire Mertens drift is being carried by four predictable family-level constants, then perhaps the right object is not the raw fluctuation sum but the centered one: subtract the family bias first, then sum only what remains.

This paper does not prove that the centered sum converges. It only isolates the structure that makes centering natural. The raw sum drifts because every family has a negative bias. Once that fact is on the table, the next question is unavoidable: if you remove the family bias, does the remaining fluctuation cancel?

That is the question the later centered papers take up. From the point of view of this note, the important thing is more basic. The drift is not random noise. It is organized. It lives in four class-specific constants, and once you see that, the divergence at $s = 1$ stops looking mysterious and starts looking removable.
## A note from 2026

*April 2026*

Looking at this paper now, three results from it became load-bearing for the formal preprints.

The bilateral parity theorem ($C(g)$ is always even) entered [the collision invariant](https://alexpetty.com/the-collision-invariant/) as one of the structural constraints that forces the antisymmetry $S(a) + S(b^2 - a) = -1$. Without the pairing of collisions under the complement map, the antisymmetry constant would not be forced to $-1$, and the negative bias of the collision periodic table would not be structural. The parity is the seed.

The exact decomposition of the deviation into an integer part and a class correction became the starting point for the centered collision sum that [the collision transform](https://alexpetty.com/the-collision-transform/) analyzes at $s = 1$. The centering in that formal preprint is exactly the centering introduced here, and the convergence at $s = 1$ proved there is the conditional version of the convergence conjectured here.

The reappearance of the constant $2/3$ from the golden ratio paper still feels significant to me. The alignment limit $\alpha = 2/3$ at the prime $3$ was the observation that started the entire program. Finding it again as the per-family collision bias for the digit-$7$ family suggests that the golden ratio's selection of the prime $3$ is not a standalone curiosity. It is wired into the family structure of the collision count at every depth. The constant connects the first rung of the program to a rung that came much later, and the fact that it appears without being placed there is the kind of structural echo that keeps me going.

.:.

---

## Try it yourself

```
$ ./nfield fluctuation_sum 10 --lag 1 --primes 10000
  base 10, lag 1
  primes scanned: 10,000
  accumulated sum: -1.60
  sum / log log p_max = -0.652
  drifting toward μ₁ ≈ 0.68

$ ./nfield class_bias 10 --lag 1
  base 10, lag 1, primes up to 10^7
  class digit 1:  mean deviation = -1.70
  class digit 3:  mean deviation = -1.11
  class digit 7:  mean deviation = -0.68  (≈ -2/3)
  class digit 9:  mean deviation = -0.12

$ ./nfield centered_sum 10 --lag 1
  centered sum at s=1: converges
  raw sum at s=1: diverges (Mertens rate)
```

Three commands. The first shows the Mertens growth. The second shows the per-family biases, including the $2/3$ at digit $7$. The third shows the centered sum converging where the raw sum diverges.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Collision Fluctuation Sum](https://github.com/alexspetty/nfield/blob/main/research/collision_fluctuation_sum.pdf)

---

*Alexander S. Petty*
April 2023 (updated April 2026)
.:.
