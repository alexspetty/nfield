# The Three-Tier Theorem

The alignment formula from [The Alignment Limit](https://alexpetty.com/the-alignment-limit-for-all-primes/) works for prime-times-smooth denominators. It already showed that the prime 3 sits above the golden line at $1/\varphi \approx 0.618$ and the other primes do not. But most integers are not of that form. To classify every integer, I needed a different argument.

The answer turned out to be sharp. Every positive integer falls into one of exactly three tiers. Above the golden line, on it, or below it. No integer sits ambiguously near the threshold. The classification is unconditional.

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

No pipes anywhere. Every decimal stops. There is no repeating block to disagree about, so by convention every fraction is treated as agreeing with $1/n$ at every position. The alignment is $1$. Smooth numbers sit at the top of the classification for a simple reason: nothing repeats, so nothing can mismatch.

## Tier 2: the golden family

Tier 2 is the golden family. These are the integers of the form $n = 3m$, where $m$ is smooth (built from $2$s and $5$s) and at least $4$. They have repeating fractions, genuine disagreements between decimal patterns, and yet their alignment stays above $1/\varphi$.

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

Four of the eleven fractions repeat the digit $3$ inside their pipes, four repeat the digit $6$, and three terminate. The alignment of $12$ comes out high.

```
$ ./nfield align 12       # 0.636
$ ./nfield align 24       # 0.652
$ ./nfield align 60       # 0.661
$ ./nfield align 120      # 0.665
```

Each value is above $0.618$. Each one climbs slowly toward the limit $2/3$. This is the same phenomenon isolated in [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/): among primes, only 3 has alignment limit above the golden threshold, and the integers in Tier 2 are exactly the integers whose rough part is 3.

The golden family is small. It is $3 \times 4$, $3 \times 5$, $3 \times 8$, $3 \times 10$, $3 \times 16$, $3 \times 20$, and so on: just the integers of the form three times a smooth number, with smooth factor at least 4.

## Tier 3: everything else

Everything else lives in Tier 3. Every prime from $5$ onward. Every composite whose rough part is anything other than $3$. Every number outside the smooth family and the golden family.

```
$ ./nfield align 7        # 0.167
$ ./nfield align 13       # 0.111
$ ./nfield align 77       # 0.088
$ ./nfield align 91       # 0.100
```

None of these is close to $0.618$. The gap between the lowest Tier 2 value and the Tier 3 values is visible even in small examples.

![The three tiers](https://alexpetty.com/content/images/2026/04/three_tier_canyon-1.png)

Every integer from 2 to 500, plotted by alignment. White at the top, the smooth numbers. Gold above the line, the golden family. Blue below, everything else. Between the gold and the blue, nothing.

## The mirror bound

The proof rests on a simple symmetry of repeating decimals. Every non-terminating fraction $k/n$ has a partner, namely $(n - k)/n$. The repeating digits of $k/n$ and the repeating digits of its partner sum to $9$ at every position. If $k/n$ has the digit $3$ at some position, then $(n-k)/n$ has $6$ there. If $k/n$ has $1$, the partner has $8$. They are mirror images in the digit system. Mathematicians call this the **nines complement**.

This symmetry has a strong consequence. At any single position, if $k/n$ matches the digit of $1/n$, then its partner $(n-k)/n$ cannot. Within each pair, at most one fraction can score a match at that position.

This bounds the average alignment over the non-terminating fractions by $1/2$. Add back the terminating fractions, which always contribute alignment $1$, and the total alignment of $n$ satisfies
$$\alpha(n) \le \frac{t + 1}{2t},$$
where $t$ is the rough part of $n$ (the prime factors not in the base).

Now a fact specific to base 10. The rough part of any integer is always coprime to 10. The integers 4, 5, and 6 all share a factor with the base, so they cannot appear as rough parts. The smallest rough part strictly larger than 3 is therefore $t = 7$. At $t = 7$, the inequality gives
$$\alpha(n) \le \frac{8}{14} = \frac{4}{7} \approx 0.571.$$
That number is below $1/\varphi \approx 0.618$. Every rough part larger than 7 gives an even smaller bound. So every integer with rough part at least 7 falls in Tier 3.

Three cases remain. For $t = 1$, the integer is smooth, so it lies in Tier 1. For $t = 3$ with $m \ge 4$, the alignment formula from earlier in the series gives
$$\alpha(3m) = \frac{2m - 1}{3m - 1} \ge \frac{1}{\varphi},$$
which puts these in Tier 2. For $t = 3$ with $m < 4$, direct computation gives $\alpha(3) = 1/2$ and $\alpha(6) = 3/5$, both below $1/\varphi$, so these belong to Tier 3.

The whole argument pivots on the gap between 3 and 7 in the rough part.

![The mirror bound](https://alexpetty.com/content/images/2026/04/three_tier_mirror_bound-1.png)

The curve is the mirror bound $(t+1)/(2t)$ as a function of the rough part $t$. At $t = 1$, the bound is 1. At $t = 3$, it is $2/3$, above the golden line. At $t = 7$, it drops to $4/7$, below the line, and it never comes back. The gap between 3 and 7 is empty because 4, 5, and 6 all share a factor with the base. No admissible rough part exists in between.

## The rough part and the smooth part

Every positive integer splits uniquely into two pieces. The **smooth part** absorbs the prime factors that the base contains. The **rough part** is everything else. In base $10$, the integer $60 = 20 \times 3$ has smooth part $20$ and rough part $3$. The integer $77 = 1 \times 77$ has smooth part $1$ and rough part $77$. The integer $8$ has smooth part $8$ and rough part $1$.

The smooth part controls the resolution of the field. It tells you how finely the field is sampled. The rough part controls the structure. It tells you which prime geometry governs the repeating digits.

The three tiers are determined entirely by the rough part.

- Rough part $= 1$. No prime structure at all. Every fraction terminates. Tier 1.
- Rough part $= 3$ with smooth part at least $4$. The golden prime governs. Tier 2.
- Anything else. Below the threshold. Tier 3.

That is the classification.

## The classification

The alignment number measures how organized an integer's fractional field is. The golden line at $1/\varphi$ sorts every integer into one of three categories, determined entirely by its rough part.

A quantity defined by comparing decimal expansions ends up depending only on one arithmetic datum: the part of the denominator the base does not already own.

---
## A note from 2026

*April 2026*

The mirror bound is the part of this paper that kept its force. Every fraction $k/n$ is paired with its complement $(n-k)/n$, and the digits of those two fractions add to $b-1$ position by position. That same involution survives almost unchanged inside [The Collision Periodic Table](https://alexpetty.com/the-collision-periodic-table/), where it becomes a reflection identity on residue classes instead of on decimal strings.

The rough part also turned out to matter more than it first seemed to. Here it controls the three-tier classification. In [The Collision Invariant](https://alexpetty.com/the-collision-invariant/) and [The Collision Periodic Table](https://alexpetty.com/the-collision-periodic-table/), the arithmetic slicing becomes finer, but the basic idea is the same: structure is carried by the part of the modulus the base does not already absorb.

Even the role of the threshold survived. The golden line at $1/\varphi$ is not the same object as the boundary at $s=1$ in [The Collision Transform](https://alexpetty.com/the-collision-transform/), but both papers are organized around a sharp dividing line that the arithmetic either clears or fails to clear. That resemblance is not a coincidence.

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

Not close. The gap between the golden family and the rest is wide. Divide out the factors of 2 and 5 from any integer. If 3 is all that remains, the alignment is above the line. If anything else remains, it is below.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Three-Tier Theorem](https://github.com/alexspetty/nfield/blob/main/research/three_tier_theorem.pdf)

---

*Alexander S. Petty*
October 2020 (updated April 2026)
.:.
