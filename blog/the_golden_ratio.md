# The Golden Ratio

*January 2010*

The golden ratio, usually written as φ (phi), is one of the more intriguing numbers in mathematics. It appears in geometry, number sequences, and a variety of natural patterns.

I have been interested in φ for a long time. What follows is a collection of notes and visualizations I have assembled while studying it. Some of this is standard material that can be found in any treatment of the subject. Some of it reflects my own way of looking at things.

## What is phi?

Phi is defined by the relationship

$$\varphi = \frac{1 + \sqrt{5}}{2}$$

Its approximate value is 1.618033...

What makes this number interesting is how it relates to itself. If you add 1 to φ, you get φ². If you subtract 1 from φ, you get 1/φ. In algebraic form:

$$\varphi^2 = \varphi + 1$$

and

$$\varphi - 1 = \frac{1}{\varphi}$$

Most numbers do not behave this way. Most numbers, when you square them or invert them, produce something unrelated to the original. Phi is different. Its square and its reciprocal are both simple transformations of itself. It is a number whose algebra is self-referential.

This self-referential quality is, I think, the reason phi keeps showing up in so many different places. It is not just a particular value. It is a relationship that regenerates itself under the most basic operations.

## Constructing phi geometrically

Phi can be constructed using simple geometry. One of the easiest ways is through a regular pentagon.

Draw a regular pentagon and connect two of its non-adjacent corners as shown below.

![Phi from a pentagon](https://alexpetty.com/content/images/2018/12/simple-construction-of-phi.png)

The ratio of lengths AB to BC in this construction is φ.

The pentagon is the simplest polygon that contains the golden ratio in its internal geometry. Every diagonal of a regular pentagon divides every other diagonal in the golden ratio. This is not a coincidence. It is a consequence of the fact that the interior angles of a pentagon (108°) are related to φ through the same quadratic equation that defines it.

## The golden triangle

Another useful figure is the golden triangle, an isosceles triangle whose sides are in the golden ratio.

![The golden triangle](https://alexpetty.com/content/images/2018/12/the-golden-triangle-2.png)

In this geometry the angles have consistent relationships, and many intersections divide segments according to the golden ratio. Most importantly, repeated subdivision of a golden triangle produces smaller golden triangles. The figure contains copies of itself at every scale.

This recursive property is one reason φ appears so frequently in pentagonal geometry. The pentagon, the pentagram, and the golden triangle are all different views of the same underlying self-similar structure.

## Phi-based geometric relationships

Additional constructions based on φ reveal many repeating relationships between angles and line segments.

![Phi geometry](https://alexpetty.com/content/images/2018/12/phi-geometry2.png)

These geometric connections help explain why the golden ratio appears in structures built from pentagons and star polygons. The relationships are not approximate. They are exact, and they follow directly from the equation φ² = φ + 1.

## Deriving phi algebraically

The golden ratio can be derived from a simple question about proportion.

If a line segment is divided so that the ratio of the whole to the larger part equals the ratio of the larger part to the smaller part, what is that ratio?

Setting up the equation gives

$$x^2 = x + 1$$

Solving produces two roots. The positive root is φ. The negative root is −1/φ.

![Algebraic derivation of phi](https://alexpetty.com/content/images/2018/12/derive-phi-algebraiclly6.png)

This equation, x² − x − 1 = 0, is the minimal polynomial of the golden ratio. It is the simplest equation that φ satisfies, and everything about φ can be derived from it. The self-referential properties, the geometric constructions, the Fibonacci connection. All of it traces back to this single quadratic.

## Viewing numbers within the unit interval

One way to visualize numbers that I find useful is to think of them as subdivisions of the interval between 0 and 1.

For example, dividing the interval into five equal parts gives

    0.0, 0.2, 0.4, 0.6, 0.8, 1.0

Dividing it into seven parts gives

    0.000000, 0.142857, 0.285714, 0.428571,
    0.571428, 0.714285, 0.857142, 1.000000

Look at the seven-part division carefully. The six interior values are all cyclic permutations of the same six digits: 142857. This is the repetend of 1/7, and every fraction k/7 is a rotation of it.

Thinking about numbers this way, as the full set of fractions with a common denominator, spread across the unit interval, can reveal patterns that are invisible when you look at individual fractions in isolation. The number 7 does not just produce the repetend 142857. It produces an entire field of six rotations of that repetend, organized symmetrically within [0, 1].

![3 as a partition](https://alexpetty.com/content/images/2018/12/3-vs-3.png)

Every integer *n* defines its own partition of the unit interval into *n* − 1 interior points. Each of those points is a fraction k/*n*, and each has its own decimal expansion. The collection of all those expansions is, in a sense, the complete arithmetic portrait of *n*.

## Phi and the Fibonacci sequence

The golden ratio is closely connected to the Fibonacci sequence:

    1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, ...

Each number is the sum of the previous two. The rule is as simple as arithmetic gets: add the last two, write down the result, repeat.

If we examine the ratios between successive Fibonacci numbers, something happens:

    1/1   = 1.000000
    2/1   = 2.000000
    3/2   = 1.500000
    5/3   = 1.666666
    8/5   = 1.600000
    13/8  = 1.625000
    21/13 = 1.615385
    34/21 = 1.619048
    55/34 = 1.617647
    89/55 = 1.618026
    144/89  = 1.617978
    233/144 = 1.618056

The ratios oscillate above and below φ, converging toward it from both sides. The simplest possible recurrence relation produces the golden ratio as its limiting behavior.

## Convergence toward phi

The chart below illustrates how the ratios of successive Fibonacci numbers converge toward φ.

![Fibonacci ratios converging on phi](https://alexpetty.com/content/images/2018/12/fibonacci-converging-on-phi5.png)

The oscillation is visible: each ratio overshoots φ, then undershoots, then overshoots again, with the amplitude decreasing each time.

## Error term of the convergence

The following diagram shows how the error between the Fibonacci ratio and φ decreases as the sequence grows.

![Error term](https://alexpetty.com/content/images/2018/12/error-term-of-fibonacci-converging-on-phi.png)

The error decreases geometrically. Each step reduces the error by a factor that itself converges to 1/φ². This is not a coincidence. It is the self-referential structure of φ expressing itself in yet another form.

## Fibonacci points on a cycle

Another way to visualize the Fibonacci sequence is to plot its values on a repeating cycle.

![Fibonacci on a cycle](https://alexpetty.com/content/images/2018/12/fib-pts-on-incr-of-12-high.png)

From a broader view the pattern becomes easier to see.

![Fibonacci on a cycle, wider view](https://alexpetty.com/content/images/2018/12/fib-pts-on-incr-of-12-high1.png)

The Fibonacci sequence, when reduced modulo a fixed number, always produces a periodic pattern. The period depends on the modulus, but the periodicity itself is guaranteed. This connects back to the [mod-9 observations](https://alexpetty.com/on-numeric-polarity-and-the-distribution-of-primes/) in my earlier post, where the Fibonacci sequence reduced modulo 9 produces a cycle of length 24 with a fixed polarity pattern.

## Why phi continues to fascinate

The golden ratio appears in pentagonal geometry, recursive subdivisions, Fibonacci growth patterns, continued fractions, and dynamical systems. It arises from the simplest quadratic equation and yet it reaches into an extraordinary range of mathematical structures.

What draws me to it is the self-referential quality. A number that contains its own inverse and its own square within a single linear transformation. A number whose defining equation is also its simplest identity. I keep finding it in places I did not expect, and I suspect there is more to find.

.:.

---

## A note from 2026

*April 2026*

I wrote this in January 2010 as a study of the golden ratio's basic properties. At the time I did not know that $\varphi$ would become the central object of my own mathematical work.

The self-referential property $\varphi^2 = \varphi + 1$ that I described here turned out to be the mechanism through which the golden ratio selects the prime $3$. The [alignment formula](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) $\alpha = (2m - 1)/(3m - 1)$ exceeds $1/\varphi$ precisely when $m \ge \varphi^2$, and this threshold emerges from the algebra of $\varphi$ itself, not from any external assumption. The minimal polynomial $x^2 - x - 1$ divides the self-referential cubic $\tau^3 - \tau^2 - 3\tau + 2 = 0$ with remainder $(3 - p)\tau$, which vanishes only at $p = 3$. The coefficient $3$ is produced by the polynomial division. The golden ratio selects the prime.

The unit interval section, where I looked at the fractions $\{k/n\}$ as a portrait of $n$, was the beginning of the fractional field that the [alignment measure](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) quantifies. The digit function $\delta(r) = \lfloor br/p \rfloor$ that sorts remainders into bins is the engine of long division, and every fraction $k/p$ is a window into that engine's output. The "complete arithmetic portrait" I described here is what the later work formalizes and measures.

I also wrote "I suspect there is more to find." The selection of the prime $3$ was the beginning. It led to the [digit-partitioning property](https://alexpetty.com/digit-partitioning-primes/), then to the [alignment limit](https://alexpetty.com/the-alignment-limit-for-all-primes/), then to the collision invariant and the polarity field, and from there to the three involutions and the structure of the critical strip. The self-referential identity $\varphi^2 = \varphi + 1$ echoes through all of it. Identity persists through transformation. That is what $\varphi$ does.

.:.

---