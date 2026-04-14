# The Three-Tier Theorem

The alignment formula from [The Alignment Limit](https://alexpetty.com/the-alignment-limit-for-all-primes/) works for every prime. It gives a number between 0 and 1, measuring how organized the fractional field is. The golden line at $1/\varphi \approx 0.618$ separates 3 from everything else. And the data from that post showed every integer above the line carrying 3 at its core.

But that was a pattern, not a proof. The formula only covers prime-times-smooth denominators. Most integers are not of that form. To classify every integer, I needed a different argument entirely.

The answer turned out to be sharp. Draw the golden line at $1/\varphi$. Every positive integer falls into one of exactly three tiers. Tier 1, alignment equal to $1$. Tier 2, alignment strictly between $1/\varphi$ and $1$. Tier 3, alignment strictly below $1/\varphi$. No exceptions. No borderline cases. No integer anywhere in the number line that sits ambiguously near the threshold. This is [proved](https://github.com/alexspetty/nfield/blob/main/research/three_tier_theorem.pdf).

## Tier 1: the smooth numbers

Some integers produce only terminating fractions. Divide anything by $8$, or $25$, or $200$, and the decimal stops. No repeating block, no cycle. These are the **smooth numbers**, integers built entirely from the prime factors of the base. In base $10$, smooth means a product of $2$s and $5$s.

```
$ ./nfield field 8
  1/8 => 0.125
  2/8 => 0.25
  3/8 => 0.375
  4/8 => 0.5
  5/8 => 0.625
  6/8 => 0.75
  7/8 => 0.875
```

No pipes anywhere. Every decimal stops. There is no repeating block to disagree about, so by convention every fraction is treated as agreeing with $1/n$ at every position. The alignment is $1$, the maximum. Smooth numbers have perfect coherence in a trivial way. There is nothing to mismatch. They sit at the top of the classification, quiet and complete, like a blank page that passes every spelling test.

## Tier 2: the golden family

Tier 2 is the place where the golden ratio actually lives. These are the integers of the form $n = 3m$, where $m$ is smooth (built from $2$s and $5$s) and at least $4$. They have repeating fractions, real structure, and genuine disagreements between their decimal patterns at certain positions. And yet, against expectation, their alignment number stays above $1/\varphi$.

The smallest example is $n = 12$. Its field has three flavors of fraction at once. Terminating, mixed, and pure repeating. The pipes mark the repeating block where there is one.

```
$ ./nfield field 12
  1/12 => 0.08|3|
  2/12 => 0.1|6|
  3/12 => 0.25
  4/12 => 0.|3|
  5/12 => 0.41|6|
  6/12 => 0.5
  7/12 => 0.58|3|
  8/12 => 0.|6|
  9/12 => 0.75
 10/12 => 0.8|3|
 11/12 => 0.91|6|
```

Four of the eleven fractions repeat the digit $3$ inside their pipes, four repeat the digit $6$, and three terminate. Most positions agree. The alignment of $12$ comes out high.

```
$ ./nfield align 12       # 0.636
$ ./nfield align 24       # 0.652
$ ./nfield align 60       # 0.661
$ ./nfield align 120      # 0.665
```

Each value above $0.618$. Each one climbing slowly toward the limit $2/3$. These denominators are governed by the prime $3$, and the prime $3$ is the one prime that the golden ratio singled out as its own. The reason is something [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) made explicit. The equation $x^2 + x = 1$ that defines the golden ratio is the same equation that selects the prime $3$ as the unique prime whose alignment limit $2/3$ exceeds $1/\varphi$. The arithmetic of the prime $3$ and the algebra of the golden ratio meet at this number, and the meeting is what fills Tier 2.

The golden family is small. It is $3 \times 4$, $3 \times 5$, $3 \times 8$, $3 \times 10$, $3 \times 16$, $3 \times 20$, and so on. Just the integers of the form three-times-a-smooth-number-at-least-four. Nothing else. But it is the only family of non-smooth integers above the line.

## Tier 3: everything else

Everything else lives in Tier 3. Every prime from $5$ onward. Every composite whose rough part (the part not coming from the base) is anything other than $3$. Every number that carries a prime factor the golden ratio cannot reach. There are infinitely many of them, including all the primes beyond $3$, all their multiples, and all their products.

```
$ ./nfield align 7        # 0.167
$ ./nfield align 13       # 0.111
$ ./nfield align 77       # 0.088
$ ./nfield align 91       # 0.100
```

Look at the numbers. $0.167$, $0.111$, $0.088$, $0.100$. None of them is close to $0.618$. They are not climbing toward it. They are not even in the same neighborhood. These values live in a different country from Tier 2. The gap between the lowest Tier 2 alignment ($0.636$ at $n = 12$) and the highest Tier 3 alignment is not a crack. It is a canyon, and $1/\varphi$ stands in the middle of it.

![The three tiers](https://alexpetty.com/content/images/2026/04/three_tier_canyon-1.png)

Every integer from 2 to 500, plotted by alignment. White at the top, the smooth numbers, perfect and silent. Gold just above the line, the golden family, every one carrying 3 at its core. Blue below, everything else. And between the gold and the blue, nothing. Five hundred integers and not a single one falls in the gap.

## The mirror bound

The proof rests on a simple symmetry of repeating decimals. Every non-terminating fraction $k/n$ has a partner, namely $(n - k)/n$. The repeating digits of $k/n$ and the repeating digits of its partner sum to $9$ at every position. If $k/n$ has the digit $3$ at some position, then $(n-k)/n$ has $6$ there. If $k/n$ has $1$, the partner has $8$. They are mirror images in the digit system. Mathematicians call this the **nines complement**.

This symmetry has a strong consequence. At any single position, the special fraction $1/n$ has some specific digit, say $5$. A fraction $k/n$ matches $1/n$ at that position only if its digit there is also $5$. But its partner $(n - k)/n$ then has digit $9 - 5 = 4$ at the same position, which is not $5$. So at most one of the two partners can match $1/n$ at any given position. The fractions of $n$ pair up, and within each pair only one half can score a match.

This bounds the average alignment over the non-terminating fractions to $1/2$. Add back the terminating fractions, which always contribute the maximum alignment $1$, and the total alignment of $n$ satisfies the inequality
$$\alpha(n) \le \frac{t + 1}{2t},$$
where $t$ is the rough part of $n$ (the prime factors not in the base).

Now a fact specific to base $10$. The rough part of any integer is always coprime to $10$. The integers $4$, $5$, and $6$ all share a factor with $10$, so they cannot appear as rough parts. The smallest rough part strictly larger than $3$ is therefore $t = 7$. At $t = 7$, the inequality gives
$$\alpha(n) \le \frac{8}{14} = \frac{4}{7} \approx 0.571.$$
That number is below $1/\varphi \approx 0.618$. Every rough part larger than $7$ gives an even smaller bound. So every integer with rough part at least $7$ falls in Tier 3.

Three small cases remain. For $t = 1$, the integer is smooth, alignment is $1$, Tier 1. For $t = 3$ with $m \ge 4$, the alignment formula from earlier in the series gives
$$\alpha(3m) = \frac{2m - 1}{3m - 1} \ge \frac{1}{\varphi},$$
which puts these in Tier 2. For $t = 3$ with $m < 4$, direct computation gives $\alpha(3) = 1/2$ and $\alpha(6) = 3/5$, both below $1/\varphi$, so these go to Tier 3.

The whole argument pivots on the gap between $3$ and $7$ in the rough part.

![The mirror bound](https://alexpetty.com/content/images/2026/04/three_tier_mirror_bound-1.png)

The curve is the mirror bound $(t+1)/(2t)$ as a function of the rough part $t$. At $t = 1$, the bound is 1. At $t = 3$, the bound is $2/3$, above the golden line. At $t = 7$, the bound drops to $4/7$, below the golden line, and it never comes back. The curve falls toward $1/2$ and stays there. The golden line cuts through the gap between $t = 3$ and $t = 7$, and the gap is empty because 4, 5, and 6 all share a factor with the base. No coprime rough part exists in between. The proof rests on this accident of arithmetic.

## The rough part and the smooth part

Every positive integer splits uniquely into two pieces. The **smooth part** absorbs the prime factors that the base contains. The **rough part** is everything else. In base $10$, the integer $60 = 20 \times 3$ has smooth part $20$ and rough part $3$. The integer $77 = 1 \times 77$ has smooth part $1$ and rough part $77$. The integer $8$ has smooth part $8$ and rough part $1$.

The smooth part controls the resolution of the field. It says how many fractions share the same repeating block, how finely the field is sampled. The rough part controls the structure. It says which prime's digit geometry governs the field, which arrangements of repeating digits occur, where the symmetries lie.

The three tiers are determined entirely by the rough part.

- Rough part $= 1$. No prime structure at all. Every fraction terminates. Tier 1.
- Rough part $= 3$ with smooth part at least $4$. The golden prime governs. Tier 2.
- Anything else. Below the threshold. Tier 3.

That is the whole classification, in three lines.

## The line that draws itself

Every positive integer has an interior. Its family of fractions, their repeating decimal patterns, their symmetries, their disagreements. The alignment number measures how organized that interior is.

Draw one horizontal line, at the height $1/\varphi$. Nobody chose this line. The algebra of the simplest self-referential equation put it there, and the algebra is the same algebra that defines the golden ratio. That single line sorts every positive integer into one of three categories.

The integers are not random when viewed from the inside. They are tiered. Silence at the top. The golden family in the middle. Everything else below, separated by a canyon so wide that no borderline case exists anywhere in the integers.

I did not set out to find this. I was measuring alignment because I wanted to understand repeating decimals, and the classification emerged from the measurements. The golden ratio was already there, waiting at the boundary. It had been waiting since it [selected the prime $3$](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/).

---

## A note from 2026

*April 2026*

The mirror bound in this post is the first appearance of the involution that runs through the entire program. Every fraction $k/n$ paired with its complement $(n-k)/n$, digits summing to $b-1$ at every position, at most one match per pair. That same pairing, lifted from digits to residue classes, becomes the [collision periodic table's](https://alexpetty.com/the-collision-periodic-table/) reflection identity $S(a) + S(m-a) = -1$. The local bound and the global antisymmetry are the same symmetry operating at different scales. Both produce a structural mean of exactly $-1/2$.

The rough part, which controls the three tiers here, prefigured the conductor structure of the recent work. The [collision invariant](https://alexpetty.com/the-collision-invariant/) classifies primes by their last two base-$b$ digits, exactly the slicing the rough part defines for general integers. The "tier" of an integer in this post and the "cell" of a prime in the collision table are determined by the same arithmetic, one level apart.

The golden line at $1/\varphi$ in this post and the boundary at $s = 1$ in the recent work are the same line in different coordinates. The [collision transform](https://alexpetty.com/the-collision-transform/) cancels at the prime number theorem boundary. The [collision spectrum](https://alexpetty.com/the-collision-spectrum/) factors through L-function values at $s = 1$. The digit function's reach, which this post measured through alignment, turned out to extend all the way to the critical strip.

.:.

---

## Try it yourself

Start with the smooth numbers. No rough prime, no repeating block, perfect alignment.

```
$ ./nfield align 8        # 1.000
$ ./nfield align 25       # 1.000
$ ./nfield align 200      # 1.000
```

Now the golden family. Rough part is 3 in every case.

```
$ ./nfield align 12       # 0.636   (= 3 × 4)
$ ./nfield align 60       # 0.661   (= 3 × 20)
$ ./nfield align 120      # 0.664   (= 3 × 40)
```

All above $0.618$. All climbing toward $2/3$. Now try anything with a different rough prime.

```
$ ./nfield align 7        # 0.167
$ ./nfield align 13       # 0.111
$ ./nfield align 77       # 0.088   (= 7 × 11)
$ ./nfield align 91       # 0.100   (= 7 × 13)
$ ./nfield align 1001     # 0.099   (= 7 × 11 × 13)
```

Not close. Not even in the same neighborhood. The canyon between $0.636$ and $0.167$ is where the golden line sits, and nothing falls inside it. Divide out the factors of 2 and 5 from any integer. If 3 is all that remains, the alignment is above the line. If anything else remains, it is below. Try to find a counterexample. You will not.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Three-Tier Theorem](https://github.com/alexspetty/nfield/blob/main/research/three_tier_theorem.pdf)

---

*Alexander S. Petty*
October 2020 (updated April 2026)
.:.
