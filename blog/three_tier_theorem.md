# The Three-Tier Theorem

You can assign a number to every positive integer. Not its size, not its prime factorization, but something more internal: how much of its fractional field holds together. How coherent the repeating decimals are. How organized the arithmetic is, viewed from inside.

When you do this, and when you draw a line at $1/\varphi$, every integer falls into one of three tiers. The classification is not gradual. It is sharp, and the line is not arbitrary. It is the golden ratio, and it sorts the integers the way a prism sorts light: cleanly, completely, and with structure on both sides of the cut. This is [proved](https://github.com/alexspetty/nfield/blob/main/research/three_tier_theorem.pdf).

## Tier 1: the smooth numbers

Some integers produce only terminating fractions. Divide anything by 8, or 25, or 200, and the decimal stops. No repeating block. No cycle. These are the smooth numbers: integers built entirely from the factors of the base. In decimal, that means products of 2s and 5s.

```
$ ./nfield field 8
  1/8 => 0.125 (open)
  2/8 => 0.25 (open)
  3/8 => 0.375 (open)
  ...
```

Every fraction terminates. Alignment is 1. These numbers have perfect coherence in a trivial way: there is nothing to disagree about. No digit repeats, so no digit can mismatch. They sit at the top of the classification, quiet and complete, like silence that scores perfectly on a harmony test.

## Tier 2: the golden family

Tier 2 is where the golden ratio lives. These are the denominators $n = 3m$ where $m$ is smooth and at least 4. They have repeating fractions, real structure, genuine collisions between digit classes. And yet their alignment stays above $1/\varphi$.

```
$ ./nfield align 12       # 0.636
$ ./nfield align 24       # 0.652
$ ./nfield align 60       # 0.661
$ ./nfield align 120      # 0.665
```

Each value above 0.618. Each one climbing, slowly, toward $2/3$. These denominators are governed by the prime 3, and the prime 3 is the one prime the golden ratio selected. The algebra from the cubic, the threshold from the inequality, the limit from the formula: they all converge here. The golden family is small. It is $3 \times 4, 3 \times 5, 3 \times 8, 3 \times 10, 3 \times 16, \ldots$ and nothing else. But it is the only family above the line.

## Tier 3: everything else

Everything else. Every prime from 5 onward. Every composite whose rough part is not 3. Every number that carries a prime factor the golden ratio cannot reach. And there are infinitely many of them: all the primes beyond 3, all their multiples, all their products.

```
$ ./nfield align 7        # 0.167
$ ./nfield align 13       # 0.111
$ ./nfield align 77       # 0.088
$ ./nfield align 91       # 0.100
```

Look at the numbers. 0.167. 0.111. 0.088. Not close to 0.618. Not approaching it. Not trending toward it. These values live in a different country from Tier 2. The gap between the lowest Tier 2 alignment (0.636 at $n = 12$) and the highest Tier 3 alignment is not a crack. It is a canyon, and $1/\varphi$ stands in the middle of it.

## The proof

The proof uses the nines complement. Every non-terminating fraction $k/n$ has a partner: $(n-k)/n$. Their repeating digits sum to 9 at every position. If $k/n$ repeats the digit 3 at some position, $(n-k)/n$ repeats 6 there. If $k/n$ has a 1, the partner has an 8. They are mirror images in the digit system.

This means they cannot both match $1/n$ at the same position. If $1/n$ has digit 3 at position 4, then $k/n$ matches there only if it also has 3, and its partner has 6 and does not match. One match per pair, at most. Half the non-terminating fractions can match at any given position.

This bounds the average non-terminating alignment to $1/2$. Add back the terminating fractions (which always contribute alignment 1) and the total alignment satisfies

$$\alpha(n) \leq \frac{t+1}{2t}$$

where $t$ is the rough part.

Now a fact specific to base 10: the rough part is always coprime to 10. The integers 4, 5, and 6 share a factor with 10, so the smallest possible rough part above 3 is $t = 7$. At $t = 7$: $(7+1)/(2 \cdot 7) = 4/7 \approx 0.571$. Below $1/\varphi \approx 0.618$. Every rough part larger than 7 gives an even smaller bound.

For $t = 3$ with small smooth part: direct computation. $\alpha(3) = 1/2$ and $\alpha(6) = 3/5$, both below $1/\varphi$.

For $t = 1$: smooth. Tier 1.

For $t = 3$ with $m \geq 4$ smooth: the alignment formula gives

$$(2m-1)/(3m-1) \geq 1/\varphi$$

Tier 2.

The entire argument pivots on the gap between 3 and 7 in the rough part. The golden ratio sits above $4/7$ and below $2/3$. The prime 3 reaches the threshold. Every rough part $\geq 7$ falls short. And nothing in between is coprime to the base.

## The rough part and the smooth part

Every integer splits uniquely into two pieces: the smooth part (absorbing the factors of the base) and the rough part (everything else). In base 10: $60 = 20 \times 3$, so the smooth part is 20 and the rough part is 3. The number $77 = 1 \times 77$: smooth part 1, rough part 77.

The smooth part controls the resolution: how many fractions share each repetend, how finely the field is sampled. The rough part controls the structure: which prime's digit geometry governs the field, which bins fill, which collisions occur.

The three tiers are determined entirely by the rough part:

- Rough part $= 1$: no prime structure at all. Termination. Tier 1.
- Rough part $= 3$, smooth part $\ge 4$: the golden prime governs. Tier 2.
- Anything else: below the threshold. Tier 3.

## What the classification means

Stand back from the details for a moment. Here is what the three-tier theorem says, in plain language.

Every positive integer has an interior. That interior is its fractional field: the collection of all fractions with that denominator, their repeating patterns, their symmetries, their collisions. The alignment measures how organized that interior is.

Now draw one line. $1/\varphi$. Not a line you chose. A line the algebra produced, from the interaction between the simplest nontrivial polynomial and the simplest nontrivial prime. And that single line sorts every positive integer into one of three categories. Every positive integer. No exceptions.

The integers are not random from the inside. They are tiered. The tiers are controlled by one constant, and the constant is the golden ratio. Silence at the top. The golden family in the middle. Everything else below, separated by a gap so wide that no borderline cases exist.

I did not set out to find this. I was measuring alignment because I wanted to understand repeating decimals. The classification emerged from the measurements, and the golden ratio was already there, waiting at the boundary, because it had been selecting the prime 3 from the beginning.

---

## A note from 2026

*April 2026*

The three-tier classification proved here completed the alignment program. The two earlier alignment papers had shown the formula and the limit; this one closed the gap by ruling out every integer above the line except the smooth numbers and the golden family. The proof's central tool, the nines complement bound on non-terminating fractions, foreshadowed the structural antisymmetry that runs through the recent work.

In the recent collision invariant program, the same nines complement appears as the [collision periodic table's](https://alexpetty.com/the-collision-periodic-table/) reflection identity: $S(a) + S(b^2 - a) = -1$ for every coprime $a$. The pairing of digits at the alignment level (each pair sums to $b - 1$, so at most one matches per position) is the local instance. The pairing of residue classes mod $b^2$ at the collision level is the global generalization. Both come from the same involution $a \mapsto m - a$, and both produce the mean of exactly $-1/2$ that runs through the entire program.

The "rough part" framing of this paper, splitting every integer into its smooth and rough components, prefigured the conductor structure of the recent work. The boundary alphabet at conductor $b^2$ classifies primes by their last two base-$b$ digits, exactly the slicing that the rough part defines for general integers. The "tier" of an integer in this paper is determined by its rough part; the cell of a prime in the recent [collision invariant](https://alexpetty.com/the-collision-invariant/) is determined by the same kind of arithmetic.

The closing image of this post, the line at $1/\varphi$ that emerges from the arithmetic of every $n$ and connects them all at the same height, is the same line the recent work has been climbing toward in different language. The collision invariant's centered sum cancels at the boundary $s = 1$ of the prime number theorem; the [collision spectrum](https://alexpetty.com/the-collision-spectrum/) factors through L-function values at $s = 1$. The line is in different coordinates, but it is the same line.

.:.

---

## Try it yourself

```
$ ./nfield align 8        # Tier 1 (smooth): 1.000
$ ./nfield align 25       # Tier 1 (smooth): 1.000
$ ./nfield align 12       # Tier 2 (3 * smooth): 0.636
$ ./nfield align 120      # Tier 2 (3 * smooth): 0.664
$ ./nfield align 7        # Tier 3: 0.167
$ ./nfield align 13       # Tier 3: 0.111
$ ./nfield align 77       # Tier 3 (composite rough): 0.088
$ ./nfield align 91       # Tier 3 (composite rough): 0.100
```

Each integer is a vessel. Its fractional field rises from it like a fountain of color, carrying the alignment upward. Some fountains are tall and coherent, their light concentrated. Others spray wide and dim. But at 0.618 of the way up, something happens in all of them: a concentration, a brightening, a star-like point where the structure gathers. These points, one per integer, bridge together across the entire landscape and form a line. The line is not drawn. It appears. It is the golden threshold, emerging from the arithmetic of every single $n$, connecting them all at the same height. Above the line: silence, and the golden family. Below: everything else, scattered but not random, governed by the same digit function, just too crowded to cohere.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Three-Tier Theorem](https://github.com/alexspetty/nfield/blob/main/research/three_tier_theorem.pdf)

---

*Alexander S. Petty*
February 2022 (updated April 2026)
.:.

