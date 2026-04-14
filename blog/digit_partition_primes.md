# Digit-Partitioning Primes and the Alignment Formula

In base 10, three primes have a property that no other prime has. 3, 7, and 11. Their fractions never collide. Take $p = 11$:

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

Ten fractions, ten two-digit blocks. Read down the first column. Every digit exactly once. Read down the second. Every digit in reverse. No two fractions share a digit at the same position. Perfect separation. Every fraction has its own lane.

Now take $p = 13$:

```
 1/13 => 0.|076923|     7/13 => 0.|538461|
 2/13 => 0.|153846|     8/13 => 0.|615384|
 3/13 => 0.|230769|     9/13 => 0.|692307|
 4/13 => 0.|307692|    10/13 => 0.|769230|
 5/13 => 0.|384615|    11/13 => 0.|846153|
 6/13 => 0.|461538|    12/13 => 0.|923076|
```

Twelve fractions, but only ten possible digits. Read the leading digits. 0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9. The digits 3 and 6 each appear twice. Two collisions. The separation breaks.

The line between these two worlds is a single inequality, $p \leq b + 1$. Below it, fewer remainders than digits. Every remainder gets its own bin. Above it, more remainders than bins, and some have to share.

I call the primes on the clean side *digit-partitioning*. In base 10, there are exactly three. 3, 7, and 11. Three primes out of infinitely many. And these three look nothing alike from the inside.

## Three primes, three mechanisms, one condition

Start with 3. The smallest odd prime. Its fractional field is as clean as it gets:

```
1/3 => 0.|3|
2/3 => 0.|6|
```

Two fractions. Two single-digit repetends. 3 and 6, sitting in separate lanes with the whole road between them. There is nothing to collide with.

Now 7. This is where it gets beautiful. You have already seen this field, but look at it differently. Don't read across. Read down:

```
1/7 => 0.|142857|
2/7 => 0.|285714|
3/7 => 0.|428571|
4/7 => 0.|571428|
5/7 => 0.|714285|
6/7 => 0.|857142|
```

Every column contains six different digits. Six fractions, six positions, and at every position, every fraction chose a different digit. The separation is total. Not because of anything deep about the number 7. Just because 7 is small enough. Six remainders, ten digit bins. There is room.

Now think about 142857. Multiply it by 2 and you get 285714. Multiply by 3 and you get 428571. By 4, 571428. The same six digits, rearranged, every time. It has appeared in recreational math books for over a century, usually without an explanation.

Here is the explanation. Each multiplication corresponds to a different fraction of 7. Each fraction's repetend is a rotation of the same string. And the rotations never collide because six remainders fit into ten bins without sharing. The cyclic property of 142857 is not a coincidence. It is forced by a single inequality, $7 \leq 10 + 1$.

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

Single digits. Full cycles. Complement pairs. Three completely different structures, one shared property. No two fractions share a digit at the same position. The condition $p \leq b + 1$ unifies them. It does not care how the separation happens. It cares only that there are enough bins.

## One formula for all three

For every digit-partitioning prime, the alignment of the fractional field has a single formula. I proved this for $p = 3$ in [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) and then found the same formula holds for every digit-partitioning prime:

$$\alpha(pm) = \frac{2m - 1}{pm - 1}$$

where $m$ is a $b$-smooth integer (its prime factors all divide the base). The formula works for $p = 3$, for $p = 7$, for $p = 11$. No correction terms, no special cases. As $m$ grows, the alignment approaches $2/p$.

Three completely different primes. Three completely different internal mechanisms. One formula. The alignment does not care how the separation happens. It cares only that it does.

## The golden ratio, again

The formula gives an alignment limit of $2/p$ for each prime. At $p = 3$, the limit is $2/3 \approx 0.667$. Above the golden threshold at $1/\varphi \approx 0.618$. At $p = 5$, the limit is $2/5 = 0.4$. Below. At $p = 7$, $2/7 \approx 0.286$. Further below. The function $2/p$ crosses $1/\varphi$ between 3 and 5, at $p = 2\varphi \approx 3.236$, and there are no primes in that gap.

The golden ratio did not choose 3 because 3 is small. It chose 3 because $1/\varphi$ lives in the gap between 3 and 5, the one place in the prime line where such a selection can happen. The algebra is in [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/).

## The last seat

The digit function takes each remainder and drops it in a bin. In base 10, there are ten bins. A prime $p$ has $p - 1$ remainders. When there are fewer remainders than bins, everyone fits. When there are more, some have to share.

![The digit function sorts remainders into bins](https://alexpetty.com/content/images/2026/04/digit_partition_bins-2.png)

The top row is the clean world. At $p = 3$, two remainders in ten bins. Nearly empty. At $p = 7$, six into ten. Room to spare. At $p = 11$, ten into ten. Every seat taken, no one standing.

The bottom row is where it breaks. At $p = 13$, twelve remainders, ten bins. Two bins turn red. At $p = 17$, more red. At $p = 23$, the remainders outnumber the bins two to one, and the red is spreading.

![Collisions explode](https://alexpetty.com/content/images/2026/04/digit_partition_collisions-2.png)

The top panel shows each prime's ten digit bins, colored by how crowded they are. At $p = 3$, $7$, and $11$, below the gold line, all blue. Zero collisions. At $p = 13$, the first red appears. At $p = 17$, $19$, $23$, more red, spreading. By $p = 499$, the bins are saturated. The bottom panel counts the total collisions. The three digit-partitioning primes sit at zero in blue. Everything after them is red, and the red grows fast.

And it never comes back. Every prime larger than 11 has collisions in base 10. The digit-partitioning world is small. Three primes. The collision world is everything else.

But collisions are not chaos. They land in specific places, governed by the same digit function, and they have structure.

Change the base and the clean primes change with it. Base 10 gives you 3, 7, and 11. Base 6 gives you 2, 3, and 5. Base 16 gives you 2, 3, 5, 7, 11, 13, and 17. Different grids, different clean primes. But the primes themselves did not change. The alignment formula $(2m - 1)/(pm - 1)$ is the same in every base. The golden threshold is the same in every base. Something underneath does not depend on which grid you chose.

What is it? What does the prime look like when you stop choosing bases and look at it directly?

---

## A note from 2026

*April 2026*

The closing question got an answer. The [collision invariant](https://alexpetty.com/the-collision-invariant/) builds a finite signed table from the digit function, one entry per coprime residue class, encoding the collision structure this post was circling around. The [collision periodic table](https://alexpetty.com/the-collision-periodic-table/) shows its antisymmetry and its mean of exactly $-1/2$. The [collision transform](https://alexpetty.com/the-collision-transform/) shows that the centered sum over primes cancels at the boundary where the prime number theorem lives. The [collision spectrum](https://alexpetty.com/the-collision-spectrum/) shows that the Fourier transform factors through L-function special values at $s = 1$. The digit function reached further than anyone expected.

The boundary at $p = b + 1$ turned out to be a real structural divide. The recent work lives entirely on the collision side. The complement pairs visible at $p = 11$ in this post, digits summing to 9 at every position, are a local instance of a global antisymmetry that governs the entire collision table. The pairing on digits became a pairing on residue classes. Same involution, larger stage.

The prime 3 kept its privileged position. The golden ratio selected it here from the alignment formula. In the recent work, the same prime is selected again from the boundary algebra. Two routes, one prime. That pattern has not stopped repeating.

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

Now change the base. The same structure, different clean primes.

```
$ ./nfield field 7 --base 6    # 7 is the boundary prime of base 6
  1/7 => 0.|05|
  2/7 => 0.|14|
  3/7 => 0.|23|
  4/7 => 0.|32|
  5/7 => 0.|41|
  6/7 => 0.|50|
```

Complement pairs again. Digits summing to 5. The same mirror, different base. Try `./nfield field 17 --base 16` and you will see it again. The boundary prime $b + 1$ always has this structure, because $b \equiv -1 \pmod{b+1}$ is always true.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Digit-Partitioning Primes and the Alignment Formula](https://github.com/alexspetty/nfield/blob/main/research/digit_partition_primes.pdf)

---

*Alexander S. Petty*
April 2020 (updated April 2026)
.:.

