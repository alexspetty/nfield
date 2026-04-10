# Why the Golden Ratio Selects the Prime Three

There is a machine hiding inside long division. You learned it as a child, and then you forgot to look at what it builds.

Take a number like 7. Divide 1 by it:

```
1/7 => 0.|142857|
2/7 => 0.|285714|
3/7 => 0.|428571|
4/7 => 0.|571428|
5/7 => 0.|714285|
6/7 => 0.|857142|
```

The pipes mark the repeating block. Look at what's inside them: it's the same six digits every time, started from a different position. 142857, rotated. Every fraction with denominator 7 carries the same pattern. The prime organizes its entire fractional field into a single repeating orbit.

Long division is a machine. You feed it a numerator and a denominator, and it produces digits. One at a time, forever if necessary. The digit it produces at each step depends on one thing: the remainder. The remainder $r$ enters the machine. The machine computes $\lfloor br/p \rfloor$ and outputs a digit. Then it passes along the new remainder, and the cycle continues. That function, $\delta(r) = \lfloor br/p \rfloor$, is the engine of everything that follows. It is the digit function.

Not all numbers do this. Divide by 12:

```
 1/12 => 0.08|3|    (mixed)
 2/12 => 0.1|6|     (mixed)
 3/12 => 0.25       (open)
 4/12 => 0.|3|      (closed)
 5/12 => 0.41|6|    (mixed)
 6/12 => 0.5        (open)
 7/12 => 0.58|3|    (mixed)
 8/12 => 0.|6|      (closed)
 9/12 => 0.75       (open)
10/12 => 0.8|3|     (mixed)
11/12 => 0.91|6|    (mixed)
```

Some fractions terminate (open). Some repeat immediately (closed). Some do both: a prefix that doesn't repeat, then a block that does (mixed). The field fractures. Coherence is partial.

This is where the program begins. Not with a theorem. With a question a computer can answer: how much of a number's fractional field holds together?

## Measuring coherence

Fix a denominator $n$. For each fraction $k/n$, compare its decimal expansion to $1/n$'s expansion, digit by digit. Count the matches. Average over all $k$. Call the result $\alpha(n)$.

For multiples of 3, the answer has a formula:

$$\alpha(3m) = \frac{2m - 1}{3m - 1}$$

where $m$ is a product of 2's and 5's, the prime factors of the base 10, and nothing else. As $m$ grows, $\alpha$ approaches $2/3$. Two thirds of the fractional field aligns. The prime 3 imposes order on decimal arithmetic, and the amount of order it imposes is exactly $2/3$.

I found the formula computationally. The proof came after. What came after the proof was stranger.

## The threshold

The golden ratio $\varphi = (1 + \sqrt{5})/2$ is the most irrational number, in a precise sense: its continued fraction converges more slowly than any other. Its reciprocal is $1/\varphi \approx 0.618$.

Ask: for which denominators does the alignment exceed $1/\varphi$?

The answer is $m \geq \varphi^2$.

That identity, $\varphi^2 = \varphi + 1$, is not assumed. It is the defining property of the golden ratio, and it falls out of the algebra when you solve the threshold inequality. The interaction between the formula $(2m-1)/(3m-1)$ and the number $1/\varphi$ produces the golden ratio's own signature equation.

## The selection

Now generalize. Replace 3 with any prime $p$. The alignment formula becomes

$$(2m-1)/(pm-1) \to 2/p$$

For the alignment to ever reach $1/\varphi$, you need $2/p > 1/\varphi$, which forces

$$p < 2\varphi \approx 3.236$$

Among primes, only 2 and 3 satisfy this. The prime 2 is trivial (every even denominator has a terminating component). So 3 is the unique prime where the golden threshold produces a nontrivial classification.

The prime 3 was not assumed to be special. The golden ratio selected it from the infinite list of primes by a computation that anyone can verify. The selection mechanism is algebraic, not numerical. It works in any base where 3 does not divide the base.

## The cubic

There is a deeper structure underneath.

Ask a stranger question: what if the threshold and the resolution it controls are the same number? What if the point where alignment kicks in is determined by the threshold itself? This self-referential condition produces a polynomial equation, a cubic, one for every prime:

$$\tau^3 - \tau^2 - p\tau + 2 = 0$$

Every prime $p \geq 3$ gives this equation a solution between 0 and 1. But for exactly three primes, the equation simplifies. At $p = 3$, it simplifies because the golden ratio's own defining equation is hiding inside it.

The golden ratio satisfies $\tau^2 + \tau - 1 = 0$. This polynomial divides the cubic when $p = 3$, and only when $p = 3$. The remainder of the division is

$$(3 - p)\tau$$

It vanishes if and only if $p = 3$. The number 3 is not put in by hand. The polynomial produces it.

At $p = 5$, the threshold is $1/\varphi^2$. Both thresholds live in the golden ratio's number field $\mathbb{Q}(\sqrt{5})$. For $p \geq 7$, the threshold is a cubic irrational. It lives in no quadratic field. The golden ratio loses its grip.

Three primes, three tiers. $p = 3$ is governed by the golden ratio itself. $p = 5$ is governed by its square. Every prime beyond 5 escapes the golden field entirely.

Picture it. A golden spiral emerging from a field of primes in darkness. The spiral passes through exactly one of them, and that one burns. The others sit nearby, untouched. The spiral is not decorative. It is a selection mechanism. The geometry feels inevitable, like a key fitting a lock.

## What I was looking at

I was looking at digit patterns. Repeating decimals. The kind of thing you see in a table in the back of an old arithmetic textbook. I wrote software to compute structural invariants of these patterns for every denominator, as high as the machine could handle.

I had been looking for connections to the golden ratio for years. In serious mathematics, phi has a reputation problem. It shows up in popular science as a mystical constant, pasted onto spirals and rectangles and flower petals, and professional mathematicians learn to look away. The association with numerology makes the number itself seem unserious.

But phi is the root of the simplest nontrivial polynomial over the integers. It is the slowest-converging continued fraction. It is the threshold between order and disorder in quasicrystal tilings. These are not aesthetic observations. They are theorems. My intuition kept saying there had to be more: the geometry of hurricanes and galaxies and water spiraling down a drain all pointed to something structural, not decorative.

What I did not expect was for the connection to be algebraic and exact. Not phi appearing in an approximation or a limit. Phi's minimal polynomial dividing a cubic, and the remainder naming a specific prime. The selection of the prime 3, the self-referential cubic, the three-tier hierarchy: these were not things I was looking for. The alignment formula was the first result of a research program that would eventually connect the digit function $\lfloor br/p \rfloor$ to Ramanujan sums, $L$-functions, and the distribution of primes.

But this is where it starts. With one formula, one ratio, and one prime that the algebra picks out on its own.

---

## A note from 2026

*April 2026*

The digit function $\delta(r) = \lfloor br/p \rfloor$ defined in this post became the engine of a research program that has run to the present. In the [collision invariant](https://alexpetty.com/the-collision-invariant/), the orbits of $\delta$ build a finite signed table indexed by the prime's last two base-$b$ digits. The [collision periodic table](https://alexpetty.com/the-collision-periodic-table/) shows the table's antisymmetry and its mean of exactly $-1/2$. The [collision transform](https://alexpetty.com/the-collision-transform/) shows that the centered sum over primes cancels at the same boundary where the prime number theorem lives. The [collision spectrum](https://alexpetty.com/the-collision-spectrum/) shows that the Fourier transform of the table factors through L-function special values at $s = 1$. None of this was visible from the 2020 alignment formula, but the digit function was already the right object to be looking at.

The selection of the prime 3 by the golden threshold turned out to be more than a poetic hint. The prime 3 plays a structurally privileged role in the later work: at conductor 3, the boundary alphabet of the digit function admits a closed-form null cocycle, an explicit formula that does not exist at other primes in the same family. The three-tier hierarchy of this post, $p = 3$, $p = 5$, and $p \geq 7$, prefigured a more general phenomenon: results that survive specifically at primes $\equiv 3 \pmod 4$, where the Legendre character is odd.

The line in this post that "what I did not expect was for the connection to be algebraic and exact" turned out to be the rule, not the exception. Every subsequent result in the program has had the same shape: an exact identity, hidden inside an elementary procedure, falling out of the algebra without approximation.

The earlier notebook posts that this 2020 work was built on remain online as the original record: [Foundational Tables of Multiplication](https://alexpetty.com/foundational-tables-of-multiplication/), [The Golden Ratio](https://alexpetty.com/the-golden-ratio/), [Geometries Hidden in the Number System](https://alexpetty.com/geometries-hidden-in-the-number-system/), [The Effect of Base on Numeric Fields](https://alexpetty.com/the-effect-of-base-on-numeric-fields/), and [Long Division and Euclid's Lemma](https://alexpetty.com/long-division-and-euclids-lemma-2/), all from 2010 and 2011. The recent papers developing the digit function's connection to L-function special values are available on [arXiv](https://arxiv.org/search/?query=petty+collision+invariant&searchtype=all) and [GitHub](https://github.com/alexspetty/nfield).

.:.

---

## Try it yourself

Build nfield (requires a C compiler and make):

```
git clone https://github.com/alexspetty/nfield.git
cd nfield && make
```

Look at the fractional field of 7. Every fraction is a rotation of the same six digits:

```
$ ./nfield field 7
  1/7 => 0.|142857| (closed)
  2/7 => 0.|285714| (closed)
  3/7 => 0.|428571| (closed)
  ...
```

One orbit. Total coherence. Now try 12:

```
$ ./nfield field 12
  1/12 => 0.08|3| (mixed)
  3/12 => 0.25 (open)
  4/12 => 0.|3| (closed)
  ...
```

The field fractures: some fractions terminate, some repeat, some do both. Coherence is partial. That difference is what $\alpha$ measures.

Now watch $\alpha$ approach 2/3 as the smooth factor grows:

```
$ ./nfield align 3       # 1.000
$ ./nfield align 6       # 0.600
$ ./nfield align 12      # 0.636
$ ./nfield align 24      # 0.652
$ ./nfield align 48      # 0.660
$ ./nfield align 96      # 0.663  ... approaching 2/3
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Why the Golden Ratio Selects the Prime Three](https://github.com/alexspetty/nfield/blob/main/research/golden_ratio_selects_prime_three.pdf)

---

*Alexander S. Petty*
January 2020 (updated March 2026)
.:.

