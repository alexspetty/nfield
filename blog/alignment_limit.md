# The Alignment Limit for All Primes

The alignment formula from [Digit-Partitioning Primes](https://alexpetty.com/digit-partitioning-primes-and-the-alignment-formula/) had one answer per prime. One limit, approached steadily as the smooth factor $m$ grew. I expected the same pattern to hold past the digit-partitioning boundary, where collisions begin. So I computed the alignment at $p = 53$ for increasing values of $m$ and waited for the numbers to settle.

They didn't settle.

The values wandered. Not randomly, but between two narrow bands, as if the sequence couldn't decide where it lived. Two of the smooth factors pushed the alignment toward $80/689$. Others pushed it toward $82/689$. The alignment limit, as a single number, did not exist.

At $p = 3$, the alignment climbs steadily to $2/3$. At $p = 7$, to $2/7$. One prime, one limit. That was the pattern I trusted. At $p = 53$, it broke.

![One prime settles. The other cannot.](https://alexpetty.com/content/images/2026/04/alignment_limit_lanes.png)

On the left, $p = 7$. The alignment converges to a single value. On the right, $p = 53$. The values zigzag between two narrow bands that never merge. The same formula, the same computation, but at $p = 53$ the sequence cannot decide where it lives. The question was why.

## Parallel lanes

When you do long division, the remainders cycle. At $p = 7$ in base 10, the cycle visits every remainder. 1, 3, 2, 6, 4, 5, and back to 1. A complete tour. One orbit. But at $p = 53$, the cycle is shorter. It visits only 13 of the 52 possible remainders before repeating. The other 39 remainders split into three more groups of 13, each a parallel copy of the first, offset to start somewhere else.

Mathematicians call these parallel copies *cosets*. Think of them as lanes on a track. The base determines the shape of the lane, its length and curvature. But the smooth factor $m$ determines which lane you start in. Change $m$ and you change lanes. Different lane, different remainders visited, different bins hit, different alignment.

I had been assuming one variable and there were two. The prime determines the track. The smooth factor picks the lane. And different lanes can have different scenery.

![Four lanes, four alignment limits](https://alexpetty.com/content/images/2026/04/alignment_limit_parallel_lanes-1.png)

Each square is a digit bin visited by that lane. The prime 53 has 52 remainders sorted into 10 bins. $52 = 5 \times 10 + 2$, so eight bins hold 5 remainders and two hold 6. The blue squares are the fives. The red squares are the sixes, the overcrowded bins where an extra remainder was forced in. Lanes 1 and 3 pass through the same mix of bins and produce the same alignment limit, $0.1161$. Lanes 2 and 4 pass through a slightly different mix and produce $0.1190$. Two pairs, two limits. That is why the oscillation chart showed two bands. The smooth factors were jumping between lane pairs, and the pairs disagreed.


## The formula

Once the lanes are visible, the formula follows. For any prime $p$, any base $b$, and any smooth $m$:

$$\alpha(pm) = \frac{m - 1 + m \cdot T(C_m) / L}{pm - 1}$$

Here $L$ is the length of the remainder cycle, how many steps before long division repeats. And $T$ is the total bin weight along the lane that $m$ puts you in. It adds up the size of every bin the lane passes through. A lane through crowded bins gets a higher $T$. A lane through sparse bins gets a lower one.

The formula from [Digit-Partitioning Primes](https://alexpetty.com/digit-partitioning-primes-and-the-alignment-formula/), $(2m-1)/(pm-1)$, is the special case where every bin holds one remainder and all lanes look the same. Past the boundary, the bins are uneven and the lanes diverge. The formula captures both worlds.

I found it computationally, by tracking alignment values across millions of denominators and noticing that the oscillations organized by lane. The proof came after. The formula is exact at every finite $m$. No limit, no approximation.

## The golden bound

The lanes complicate the exact value of the alignment. They do not complicate the bound.

For any lane, any $m$, and any prime $p \ge 5$:

$$\alpha(pm) < \frac{1}{\varphi}$$

Each remainder contributes at most $\lceil(p-1)/b\rceil$ to the bin sum. This gives

$$\alpha \le \frac{p+1}{2p}$$

which falls below $1/\varphi$ for all $p \ge 5$.

The golden ratio's selection of the prime 3, proved in [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/), extends to all primes unconditionally. No matter which lane you land in, no matter how large $m$ grows, no prime beyond 3 reaches the golden threshold. The lanes wander. The bound does not.

But the formula sees one prime at a time. Multiply 7 by 13 and you get 91, and the formula goes quiet. So I computed the alignment of 91 directly. Then 143. Then 1001. Then thousands more. Every one fell below the golden line. But a pattern was emerging. The integers above the line had something in common. Divide out the factors of 2 and 5, the primes the base owns, and what was left was always 3. Always. Every integer I tested above the golden line carried 3 at its core.

---

## A note from 2026

*April 2026*

The collision count that the [collision invariant](https://alexpetty.com/the-collision-invariant/) builds from the digit function is a direct descendant of the bin sum $S$ in this post. Wherever two remainders share a bin, the collision invariant records it. The digit-partitioning primes are exactly the primes where the count is zero. The bin sum $S$ is the obstruction, and it became the diagonal entry of a much larger table.

The lanes that split the alignment limit at $p = 53$ were the first hint of a deeper structure. In the [collision periodic table](https://alexpetty.com/the-collision-periodic-table/), the lane dependence becomes the cell structure of a finite table indexed by the prime's last two base-$b$ digits. Each prime sits in one cell. The four lanes at $p = 53$ correspond to four different positions inside that table. The oscillation this post discovered was the periodic table trying to show itself through the alignment.

The golden bound in this post and the antisymmetry of the [collision transform](https://alexpetty.com/the-collision-transform/) come from the same place. Every fraction $k/n$ has a mirror partner $(n-k)/n$ whose digits are complementary. That pairing is what caps the alignment here. The same pairing, lifted to residue classes, is what forces $S(a) + S(m-a) = -1$ in the collision table. The lanes wander, but the mirror holds them all.

The question posed in [Digit-Partitioning Primes](https://alexpetty.com/digit-partitioning-primes-and-the-alignment-formula/), what does the prime look like when you stop choosing bases, is answered partially here and completely in the [collision spectrum](https://alexpetty.com/the-collision-spectrum/). The bin sum $S$ turns out to be one component of a larger object whose other components are L-function special values at $s = 1$. The digit function reaches further than this post knew.

.:.

---

## Try it yourself

Watch the hidden variable appear. At $p = 53$, the alignment should converge to a single limit as $m$ grows. It doesn't:

```
$ ./nfield align 53       # 0.0991
$ ./nfield align 106      # 0.1106  (m=2)
$ ./nfield align 212      # 0.1119  (m=4)
$ ./nfield align 265      # 0.1157  (m=5, different lane)
$ ./nfield align 530      # 0.1144  (m=10, back again)
```

Four lanes. The values wander between them. Now try $p = 3$:

```
$ ./nfield align 3        # 1.000
$ ./nfield align 6        # 0.600
$ ./nfield align 12       # 0.636
$ ./nfield align 24       # 0.652
$ ./nfield align 96       # 0.663
```

One lane. Steady climb to $2/3 \approx 0.667$. Above the golden threshold at $1/\varphi \approx 0.618$. The prime 53 never comes close.

Now try integers the formula cannot reach. These have more than one rough prime:

```
$ ./nfield align 91       # 0.100   (= 7 × 13)
$ ./nfield align 143      # 0.094   (= 11 × 13)
$ ./nfield align 1001     # 0.099   (= 7 × 11 × 13)
```

All below 0.1. The golden line is at 0.618. Not even in the same world. Now try multiples of 3 with smooth factors:

```
$ ./nfield align 12       # 0.636   (= 3 × 4)
$ ./nfield align 60       # 0.661   (= 3 × 20)
$ ./nfield align 120      # 0.664   (= 3 × 40)
```

All above the line. Now divide out the factors of 2 and 5 from each one. In base 10, 2 and 5 are the base's own primes; they control whether fractions terminate, not whether they collide. They are the smooth part, the resolution, the lens. What remains after you remove them is the rough part, the arithmetic core that determines the structure. $12 = 4 \times 3$. $60 = 20 \times 3$. $120 = 40 \times 3$. The number left behind is always 3.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Alignment Limit for All Primes](https://github.com/alexspetty/nfield/blob/main/research/alignment_limit.pdf)

---

*Alexander S. Petty*
July 2020 (updated April 2026)
.:.
