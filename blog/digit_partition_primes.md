# Digit-Partitioning Primes and the Alignment Formula

Some primes enforce a kind of total order on the fractions they govern. Take $p = 11$ in base 10:

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

Ten fractions, ten two-digit blocks. Read down the first column: every digit exactly once. Read down the second: every digit in reverse. No two fractions share a digit at the same position. Perfect separation. Every fraction has its own lane.

Now take $p = 13$:

```
 1/13 => 0.|076923|     7/13 => 0.|538461|
 2/13 => 0.|153846|     8/13 => 0.|615384|
 3/13 => 0.|230769|     9/13 => 0.|692307|
 4/13 => 0.|307692|    10/13 => 0.|769230|
 5/13 => 0.|384615|    11/13 => 0.|846153|
 6/13 => 0.|461538|    12/13 => 0.|923076|
```

Twelve fractions, but only ten possible digits. Read the leading digits: 0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9. The digits 3 and 6 each appear twice. Two collisions. The separation breaks.

The line between these two worlds is a single inequality: $p \leq b + 1$.

When $p \leq b + 1$, there are at most $b$ remainders mapping into $b$ digit values, and the digit function is injective. No collisions. Every remainder gets its own digit. When $p > b + 1$, there are more remainders than digits, and the pigeonhole principle does what it always does.

I call the primes on the clean side *digit-partitioning*. The characterization is simple and, as far as I know, new: a prime is digit-partitioning in base $b$ if and only if $p \leq b + 1$. In base 10, there are exactly three: 3, 7, and 11. Three primes out of infinitely many. And these three look nothing alike from the inside.

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

Every column contains six different digits. Six fractions, six positions, and at every position, every fraction chose a different digit. The separation is total.

Why does this happen? Think about what the digit function actually does. It takes each remainder and assigns it a digit. In base 10, there are ten possible digits: 0 through 9. The prime 7 has six remainders: 1 through 6. Six items into ten slots. Every remainder can land in its own slot. No two remainders are forced to share a digit.

That is what digit-partitioning means. The digit function partitions the remainders so cleanly that no two share a bin. Not because of anything deep about the number 7. Just because 7 is small enough. Six is less than ten. There is room.

Now think about what this means for 142857. Multiply it by 2 and you get 285714. Multiply by 3: 428571. By 4: 571428. The same six digits, rearranged, every time. It has appeared in recreational mathematics books for over a century, usually without an explanation.

Here is the explanation. Each multiplication corresponds to a different fraction of 7. Each fraction's repetend is a rotation of the same string. And the rotations never collide because the digit function is injective: there are more digit values than remainders. The cyclic property of 142857 is not a coincidence. It is forced by the fact that $7 \leq 10 + 1$. In base 5, where 7 would have more remainders than digits, the clean separation breaks. But the magic does not disappear. It reappears at a different prime, one small enough for base 5 to accommodate. The structure is not a property of any particular number. It is a relationship between a prime and a base, and beneath both, the arithmetic substrate that the numeral systems approximate but do not own.

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

Ten fractions, ten two-digit blocks. Read down the first column: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9. Every digit exactly once. Read down the second column: 9, 8, 7, 6, 5, 4, 3, 2, 1, 0. The same digits in reverse.

This is not an accident. In base 10, $10 \equiv -1 \pmod{11}$. Multiplying a remainder by 10 is the same as negating it. So the second digit of each repetend comes from the mirror of the first. The digit function forces the two digits to sum to 9:

$$\lfloor 10r/11 \rfloor + \lfloor 10(11{-}r)/11 \rfloor = 9$$

The fraction $k/11$ paired with $(11{-}k)/11$ swaps the two digits, because complementing $k$ reverses the cycle. 09 becomes 90. 18 becomes 81. The outward path and its mirror.

If you read my [earlier notes on arithmetic foundations](https://alexpetty.com/arithmetic-foundations/), you will recognize this pattern. The palindromic oscillation, the expansion and contraction along mirror paths, the breathing: it is the same $k \leftrightarrow n{-}k$ complement symmetry, now visible inside the repetend structure of a single prime.

Single digits. Full cycles. Complement pairs. Three completely different structures, and yet the same property holds in all three: no two fractions share a digit at the same position. The digit function is injective. There are enough output values to go around. That is the only thing that matters, and it holds precisely when $p \leq b + 1$.

The condition $p \leq b + 1$ unifies them. It does not care which mechanism produces the separation. It cares only that there are enough digits to go around.

## The formula

For every digit-partitioning prime, the alignment of the fractional field has a single formula. I proved this for $p = 3$ in the companion paper and then found it holds universally:

$$\alpha(pm) = \frac{2m - 1}{pm - 1}$$

where $m$ is a $b$-smooth integer (its prime factors all divide the base). The formula works for $p = 3$, for $p = 7$, for $p = 11$. No correction terms, no special cases. As $m$ grows, the alignment approaches $2/p$.

This universality is the point. The alignment formula does not see the internal mechanism of the prime. It sees only the digit-partitioning property, which is a statement about the digit function's injectivity. Everything else follows.

## The golden ratio, again

Among primes $p \geq 3$, the alignment limit $2/p$ exceeds $1/\varphi$ only for $p = 3$. The prime 5 falls below the golden threshold. The prime 7 falls further. Every prime beyond 3 sits on the wrong side of the line.

The golden ratio did not choose 3 because 3 is small. It chose 3 because the function $2/p$ crosses $1/\varphi$ between 3 and 5, and there are no primes in that gap. The crossing point is $p = 2\varphi \approx 3.236$. The golden ratio lives in the gap between the primes 3 and 5. It inhabits the only space where such a selection can happen. (The algebra: [Why the Golden Ratio Selects the Prime Three](https://github.com/alexspetty/nfield/blob/main/research/golden_ratio_selects_prime_three.pdf), Sections 5 and 6.)

## Where collisions begin

Go back to the counting argument. The digit function has $b$ possible output values (the digits 0 through 9 in base 10). A prime $p$ has $p - 1$ remainders. When $p - 1 \leq b$, every remainder fits in its own slot. When $p - 1 > b$, some have to share.

The last prime where everyone fits is $p = 11$. Ten remainders, ten digits. The tightest possible fit. Every seat in the room is taken and no one is standing. That is why the complement pairs at 11 are so perfect: there is exactly one way to fill ten slots with ten items, and the mirror symmetry of $10 \equiv -1 \pmod{11}$ dictates the arrangement. This is not special to base 10. Every base $b$ has its own version of 11: the prime $b + 1$, the last one that fits. In base 6, it is 7. In base 12, it is 13. Each one sits at the boundary, and each one has complement pairs, because $b \equiv -1 \pmod{b+1}$ is always true.

At $p = 13$, the room is overcrowded. Twelve remainders, ten digits. Two remainders have to double up. Look at the field of 13 again: the digits 3 and 6 each appear twice among the leading digits. Those are the collisions. They are small here, just two, but they are the beginning of something. At $p = 101$, there are a hundred remainders in ten slots. The collisions dominate. The clean separation is a distant memory.

And it never comes back. Every prime larger than 11 has collisions in base 10. The digit-partitioning world is small: three primes. The collision world is everything else.

But collisions are not chaos. They have structure. The number of collisions, and where they occur, is governed by the bin sizes of the digit function, and the bin sizes follow a precise formula. The squared bin sizes $\sum n_d^2$ measure exactly how much collision a prime carries, and that quantity controls the alignment.

Change the base and the digit-partitioning primes change with it. Base 10 gives you 3, 7, and 11. Base 6 gives you 2, 3, and 5. Base 16 gives you 2, 3, 5, 7, 11, 13, and 17. Different lenses, different clean primes. But the primes themselves did not change. The prime 7 has the same remainders, the same orbits, the same internal relationships regardless of how you write it down. What changed is which primes the base can resolve without collision.

This observation shaped everything that followed. The digit-partitioning condition is not a fact about primes. It is a fact about the interaction between a prime and a coordinate system. The base is not revealing structure. It is imposing a grid, and the structure shows through the grid differently depending on how fine the grid is.

On one side of the boundary, the grid is fine enough. Every remainder has its own cell. The image is clean. On the other side, remainders share cells, and the image develops interference patterns. But the interference is not noise. It is the same structure, seen through a coarser grid. The collisions land in specific places, governed by the same digit function, following the same equations.

So there is something underneath all of this that does not depend on the base. Some quantity that the digit function measures, crudely or finely depending on the resolution available, but that belongs to the prime alone. The alignment formula $(2m - 1)/(pm - 1)$ is the same in every base. The golden threshold is the same in every base. The collision structure changes with the base, but the quantity it approximates does not.

What is that quantity? What does the prime look like when you stop choosing bases and look at it directly? That question is what kept me going.

---

## A note from 2026

*April 2026*

The closing question of this post, what does the prime look like when you stop choosing bases and look at it directly, was answered by the collision invariant program. The answer is a base-relative finite signed table attached to every base, encoding exactly the collision structure this post hints at. The recent papers walk through it: the [collision invariant](https://alexpetty.com/the-collision-invariant/) builds the table from the digit function $\delta(r) = \lfloor br/p \rfloor$, the [collision periodic table](https://alexpetty.com/the-collision-periodic-table/) names its antisymmetry and its mean of exactly $-1/2$, the [collision transform](https://alexpetty.com/the-collision-transform/) shows that its centered sum over primes cancels at the boundary where the prime number theorem lives, and the [collision spectrum](https://alexpetty.com/the-collision-spectrum/) shows that its Fourier transform factors through L-function special values at $s = 1$.

The condition $p \le b + 1$ identified in this post separates two regimes. Inside the regime, the digit function is injective and the three-mechanism story plays out cleanly. Outside the regime, the digit function has bin sizes greater than one, and remainders are forced to share. The recent work focuses on the second regime. The collision count $C(g)$ measures exactly how many remainders end up sharing a bin with their image under multiplication by $g$, and the signed deviation $S(p) = C(b \bmod p) - \lfloor (p-1)/b \rfloor$ became the central object of the program. The "Where collisions begin" section of this post is the seed of the collision invariant.

The "three completely different structures, and yet the same property holds in all three" observation prefigured a deeper unification. The complement-pair structure visible at the boundary prime $p = b + 1$ (digit pairs summing to $b - 1$ in any base) is a special case of a more general antisymmetry: $S(a) + S(b^2 - a) = -1$ on the entire collision invariant table at conductor $b^2$, for every coprime $a$. The pairing on digits is the local instance. The pairing on residue classes is the global generalization. Both come from the same involution $a \mapsto b^2 - a$.

The digit-partitioning prime $p = 3$, the smallest of the three in base 10, plays a structurally privileged role in the recent work. The boundary alphabet at conductor 3 admits a closed-form null cocycle that does not exist at other primes in the same family. The selection of $p = 3$ by the golden ratio in the [companion paper](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) prefigured this privileged role: the prime that the golden ratio identifies is also the one whose collision boundary admits an exact, hand-computable structural formula.

.:.

---

## Try it yourself

The three digit-partitioning primes in base 10, and the first collision:

```
$ ./nfield field 3    # two fractions, two digits
$ ./nfield field 7    # full cycle, perfect separation
$ ./nfield field 11   # boundary: complement pairs
$ ./nfield field 13   # collisions begin
```

The boundary prime in other bases. The same mirror symmetry, every time:

```
$ ./nfield field 7 --base 6    # 7 is the 11 of base 6
  1/7 => 0.|05|
  2/7 => 0.|14|
  3/7 => 0.|23|
  4/7 => 0.|32|
  5/7 => 0.|41|
  6/7 => 0.|50|

$ ./nfield field 17 --base 16  # 17 is the 11 of base 16
  1/17 => 0.|0.15|
  2/17 => 0.|1.14|
  ...
  16/17 => 0.|15.0|
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Digit-Partitioning Primes and the Alignment Formula](https://github.com/alexspetty/nfield/blob/main/research/digit_partition_primes.pdf)

---

*Alexander S. Petty*
March 2020 (updated April 2026)
.:.

