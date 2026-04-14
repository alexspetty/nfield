# The Alignment Limit for All Primes

The alignment formula from [Digit-Partitioning Primes](https://alexpetty.com/digit-partitioning-primes-and-the-alignment-formula/) had a simple shape. For each prime, there was one number to aim at, and as the smooth factor grew the alignment moved toward it. I expected the same pattern to continue past the digit-partitioning boundary, where collisions begin. So I computed the alignment at $p = 53$ for increasing smooth factors and waited for the numbers to settle.

They did not settle.

The values oscillated between two narrow bands. Some smooth factors pushed the alignment toward $80/689$. Others pushed it toward $82/689$. The alignment limit, as a single number, did not exist.

At $p = 3$, the alignment climbs steadily to $2/3$. At $p = 7$, to $2/7$. One prime, one limit. At $p = 53$, that pattern failed.

![One prime settles. The other cannot.](https://alexpetty.com/content/images/2026/04/alignment_limit_lanes.png)

On the left, $p = 7$. The alignment converges to a single value. On the right, $p = 53$. The values oscillate between two bands that never merge. The question was why.

## Parallel lanes

When you do long division, the remainders cycle. At $p = 7$ in base 10, the cycle visits every remainder: one orbit, one tour. But at $p = 53$, the cycle is shorter. It visits only 13 of the 52 possible remainders before repeating. The other 39 remainders split into three more groups of 13, each a parallel copy of the first, starting somewhere else.

Mathematicians call these parallel copies *cosets*. Think of them as lanes on a track. The base determines the track. The smooth factor $m$ determines which lane you start in. Change $m$, and you may change lanes. Different lane, different remainders visited, different bins hit, different alignment.

I had been assuming there was one variable, but there were really two. The prime determines the track. The smooth factor picks the lane.

![Four lanes, four alignment limits](https://alexpetty.com/content/images/2026/04/alignment_limit_parallel_lanes-1.png)

Each square is a digit bin visited by that lane. The prime 53 has 52 remainders sorted into 10 bins. Since $52 = 5 \times 10 + 2$, eight bins hold 5 remainders and two hold 6. The blue squares are the fives. The red squares are the sixes. Lanes 1 and 3 pass through the same mix of bins and produce the same alignment limit, $0.1161$. Lanes 2 and 4 pass through a slightly different mix and produce $0.1190$. The oscillation chart therefore splits into two bands.


## The formula

Once the lanes are visible, the formula becomes simple. For any prime $p$, any base $b$, and any smooth $m$:

$$\alpha(pm) = \frac{m - 1 + m \cdot T(C_m) / L}{pm - 1}$$

Here $L$ is the length of the remainder cycle, the number of steps before long division repeats. And $T$ is the total bin weight along the lane that $m$ puts you in. It adds up the size of every bin the lane passes through. A lane through crowded bins gets a higher $T$. A lane through sparse bins gets a lower one.

The formula from [Digit-Partitioning Primes](https://alexpetty.com/digit-partitioning-primes-and-the-alignment-formula/), $(2m-1)/(pm-1)$, is the special case where every bin holds one remainder and all lanes look the same. Past the boundary, the bins are uneven and the lanes diverge. The same exact formula now handles both worlds.

## The golden bound

The lanes complicate the exact value of the alignment. They do not complicate the bound.

For any lane, any $m$, and any prime $p \ge 5$:

$$\alpha(pm) < \frac{1}{\varphi}$$

Each remainder contributes at most $\lceil(p-1)/b\rceil$ to the bin sum. This gives

$$\alpha \le \frac{p+1}{2p}$$

because $b \ge 2$ forces $\lceil(p-1)/b\rceil \le (p-1)/2$.
That falls below $1/\varphi$ for all $p \ge 5$.

The golden ratio's selection of the prime 3, proved in [Why the Golden Ratio Selects the Prime Three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/), extends to all primes unconditionally. No matter which lane, and no matter how large $m$ grows, no prime beyond 3 reaches the golden threshold.

But the formula sees one prime at a time. Multiply 7 by 13 and you get 91, and the formula has nothing to say. So I computed the alignment of 91 directly. Then 143. Then 1001. Then thousands more. Every one fell below the golden line. The integers above the line had something in common. Divide out the factors of 2 and 5, the primes the base owns, and what was left was always 3. Every integer I tested above the golden line carried 3 at its core.

---
## A note from 2026

*April 2026*

[The Collision Invariant](https://alexpetty.com/the-collision-invariant/) returns to the same digit bins and counts what this paper only hints at: where different residues are forced to share them. In that light, the lane picture at $p=53$ looks less like an isolated quirk and more like the first sign that the digit function is organizing residues into a finite geometry.

[The Collision Periodic Table](https://alexpetty.com/the-collision-periodic-table/) makes that geometry explicit. The dependence on the lane in this paper becomes dependence on a cell in a finite table indexed by the last two base-$b$ digits of the prime. The phenomenon is the same in spirit, but far sharper in form.

The mirror pairing is also already here. Every fraction $k/n$ has a partner $(n-k)/n$ whose digits are complementary. That pairing is what keeps the alignment bounded in this paper. The same pairing, lifted from digits to residue classes, becomes one of the fixed symmetries in [The Collision Periodic Table](https://alexpetty.com/the-collision-periodic-table/) and [The Collision Transform](https://alexpetty.com/the-collision-transform/).

So the alignment limit now reads as an early structural paper. It still looks at a scalar quantity, but the scalar is already carrying the outline of the finite object that appears later.

.:.

---

## Try it yourself

Watch the hidden variable appear. At $p = 53$, the alignment does not converge to a single limit:

```
$ ./nfield align 53       # 0.0991
$ ./nfield align 106      # 0.1106  (m=2)
$ ./nfield align 212      # 0.1119  (m=4)
$ ./nfield align 265      # 0.1157  (m=5, different lane)
$ ./nfield align 530      # 0.1144  (m=10, back again)
```

The values move between the lanes. Now try $p = 3$:

```
$ ./nfield align 3        # 1.000
$ ./nfield align 6        # 0.600
$ ./nfield align 12       # 0.636
$ ./nfield align 24       # 0.652
$ ./nfield align 96       # 0.663
```

One lane. Steady climb to $2/3 \approx 0.667$. Above the golden threshold at $1/\varphi \approx 0.618$. The prime 53 never comes close. Now try multiples of 3 with smooth factors:

```
$ ./nfield align 12       # 0.636   (= 3 × 4)
$ ./nfield align 60       # 0.661   (= 3 × 20)
$ ./nfield align 120      # 0.664   (= 3 × 40)
```

All above the line. The prime 3 is the only prime whose alignment limit can cross the golden threshold.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Alignment Limit for All Primes](https://github.com/alexspetty/nfield/blob/main/research/alignment_limit.pdf)

---

*Alexander S. Petty*
July 2020 (updated April 2026)
.:.
