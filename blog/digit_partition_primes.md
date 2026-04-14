# Digit-Partitioning Primes and the Alignment Formula

Write out all ten fractions of 11 and read down the columns:

```
 1/11 => 0.|09|
 2/11 => 0.|18|
 3/11 => 0.|27|
 4/11 => 0.|36|
 5/11 => 0.|45|
 6/11 => 0.|54|
 7/11 => 0.|63|
 8/11 => 0.|72|
 9/11 => 0.|81|
10/11 => 0.|90|
```

Ten fractions, ten two-digit blocks. Every digit appears exactly once in each column. No two fractions share a digit at the same position. The separation is total.

Now try $p = 13$:

```
 1/13 => 0.|076923|     7/13 => 0.|538461|
 2/13 => 0.|153846|     8/13 => 0.|615384|
 3/13 => 0.|230769|     9/13 => 0.|692307|
 4/13 => 0.|307692|    10/13 => 0.|769230|
 5/13 => 0.|384615|    11/13 => 0.|846153|
 6/13 => 0.|461538|    12/13 => 0.|923076|
```

Twelve fractions, but only ten possible digits. Read the leading digits. 0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9. The digits 3 and 6 each appear twice. The separation is gone.

The line between these two cases is a single inequality, $p \leq b + 1$. At or below it, there are no more remainders than digit bins, so separation is possible. Above it, there are more remainders than bins, and some must share.

I call the primes on the clean side *digit-partitioning*. In base 10, there are exactly three: 3, 7, and 11.

## Three primes, three mechanisms, one condition

Start with 3. The smallest odd prime. Its fractional field is as clean as it gets:

```
1/3 => 0.|3|
2/3 => 0.|6|
```

Two fractions. Two single-digit repetends. 3 and 6. There is nothing to collide with.

Now 7. Read the columns instead of the rows:

```
1/7 => 0.|142857|
2/7 => 0.|285714|
3/7 => 0.|428571|
4/7 => 0.|571428|
5/7 => 0.|714285|
6/7 => 0.|857142|
```

Every column contains six different digits. Six fractions, six positions, and at every position, every fraction chose a different digit. The separation is total. Not because 7 is mysterious, but because 7 is small enough: six remainders, ten digit bins, and room to keep them apart.

Now think about 142857. Multiply it by 2 and you get 285714. Multiply by 3 and you get 428571. By 4, 571428. The same six digits, rearranged, every time. It has appeared in recreational math books for over a century, usually without an explanation.

Here is the explanation. Each multiplication corresponds to a different fraction of 7. Each fraction's repetend is a rotation of the same string. And the rotations never collide because six remainders fit into ten bins without sharing. The separation is forced by the inequality $7 \leq 10 + 1$; the cyclic structure comes from the multiplicative order of 10 modulo 7.

Now 11. A third mechanism, completely unlike the other two:

```
 1/11 => 0.|09|
 2/11 => 0.|18|
 3/11 => 0.|27|
 4/11 => 0.|36|
 5/11 => 0.|45|
 6/11 => 0.|54|
 7/11 => 0.|63|
 8/11 => 0.|72|
 9/11 => 0.|81|
10/11 => 0.|90|
```

Ten fractions, ten two-digit blocks. Read down the first column. 0, 1, 2, 3, 4, 5, 6, 7, 8, 9. Every digit exactly once. Read down the second column. 9, 8, 7, 6, 5, 4, 3, 2, 1, 0. The same digits in reverse.

This is not an accident. In base 10, $10 \equiv -1 \pmod{11}$. Multiplying a remainder by 10 is the same as negating it. The digit function forces each pair of digits to sum to 9:

$$\lfloor 10r/11 \rfloor + \lfloor 10(11{-}r)/11 \rfloor = 9$$

09 becomes 90. 18 becomes 81. 27 becomes 72. Every fraction paired with its complement, the outward path and its mirror. The same $k \leftrightarrow n{-}k$ symmetry visible in the [early arithmetic notes](https://alexpetty.com/arithmetic-foundations/), now showing up inside the repetend structure of a single prime.

Single digits. Full cycles. Complement pairs. Three different structures, one shared property. The condition $p \leq b + 1$ does not depend on how the separation happens, only on whether there are enough bins.

## One formula for all three

Three primes, three completely different internal mechanisms. But the alignment formula does not care how the separation happens. It cares only that it does. For every digit-partitioning prime:

$$\alpha(pm) = \frac{2m - 1}{pm - 1}$$

where $m$ is a $b$-smooth integer (built from the base's own prime factors). I proved this for $p = 3$ in [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) and then found the same formula holds at $p = 7$ and $p = 11$. No correction terms, no special cases. As $m$ grows, the alignment approaches $2/p$.

## The golden ratio, again

At $p = 3$, the limit is $2/3 \approx 0.667$. Above the golden threshold at $1/\varphi \approx 0.618$. At $p = 5$, $2/5 = 0.4$. Below. At $p = 7$, $2/7 \approx 0.286$. Further below. The function $2/p$ crosses $1/\varphi$ between 3 and 5, at $p = 2\varphi \approx 3.236$, and there are no primes in that gap.

## The last seat

The digit function takes each remainder and drops it in a bin. In base 10, there are ten bins. A prime $p$ has $p - 1$ remainders. When there are fewer remainders than bins, everyone fits. When there are more, some have to share.

![The digit function sorts remainders into bins](https://alexpetty.com/content/images/2026/04/digit_partition_bins-2.png)

In the clean cases, the remainders fit inside the available bins. At $p = 3$, there are two remainders in ten bins. At $p = 7$, six into ten. At $p = 11$, ten into ten. The bins are full, but not overcrowded.

Once the boundary is crossed, sharing begins. At $p = 13$, twelve remainders, ten bins. Two bins turn red. At $p = 17$, more red. At $p = 23$, the remainders outnumber the bins two to one.

![Collisions explode](https://alexpetty.com/content/images/2026/04/digit_partition_collisions-2.png)

The diagram shows each prime's ten digit bins, colored by how crowded they are. At $p = 3$, $7$, and $11$, below the gold line, all blue: zero collisions. At $p = 13$, the first red appears. At $p = 17$, $19$, and $23$, more bins are shared. By $p = 499$, the crowding is heavy. A second plot counts the total collisions.

And it never comes back. Every prime larger than 11 has collisions in base 10.

But collisions are not chaos. They land in specific places, governed by the same digit function, and they have structure.

Change the base and the clean primes change with it. Base 10 gives you 3, 7, and 11. Base 6 gives you 2, 3, and 5. Base 16 gives you 2, 3, 5, 7, 11, 13, and 17. Different grids, different clean primes. But the alignment formula $(2m-1)/(pm-1)$ is the same in every base. The golden threshold is the same in every base. Something underneath does not depend on which grid you chose.

What is it? What does the prime look like when you stop choosing bases and look at it directly?

---
## A note from 2026

*April 2026*

The boundary at $p=b+1$ turned out to be more than a tidy counting fact. It is the place where the program splits in two. On one side sit the clean cases from this paper. On the other side sit the collisions. [The Collision Invariant](https://alexpetty.com/the-collision-invariant/) makes that second side finite and visible, [The Collision Periodic Table](https://alexpetty.com/the-collision-periodic-table/) shows its antisymmetry, [The Collision Transform](https://alexpetty.com/the-collision-transform/) carries it to the prime number theorem boundary, and [The Collision Spectrum](https://alexpetty.com/the-collision-spectrum/) identifies the Fourier coefficients with $L$-function data at $s=1$.

That makes this paper feel different in retrospect. The counting argument here is elementary, but it is already drawing the line the rest of the work has to cross. Even the complement pairs at $p=11$, the digits summing to $9$ in every position, are an early glimpse of the same reflection that later becomes structural in [The Collision Periodic Table](https://alexpetty.com/the-collision-periodic-table/).

The role of the prime $3$ also held up. [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) picks it out from the alignment side. The conductor-$b^2$ papers pick it out again from the boundary algebra. The agreement between those two routes is one of the reasons this boundary still feels important.

.:.

---

## Try it yourself

See the three mechanisms. Each one different, each one clean.

```
$ ./nfield field 3     # single digits. 3 and 6. Nothing to collide with.
$ ./nfield field 7     # full cycle. Read down the columns. Six different digits in each.
$ ./nfield field 11    # complement pairs. Digits sum to 9. The tightest possible fit.
```

Now cross the boundary.

```
$ ./nfield field 13    # twelve remainders, ten bins. The digits 3 and 6 appear twice.
$ ./nfield field 17    # sixteen remainders. More doubles.
$ ./nfield field 23    # twenty-two remainders. The bins are crowding.
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Digit-Partitioning Primes and the Alignment Formula](https://github.com/alexspetty/nfield/blob/main/research/digit_partition_primes.pdf)

---

*Alexander S. Petty*
April 2020 (updated April 2026)
.:.
