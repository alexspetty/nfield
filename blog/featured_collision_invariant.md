# The Collision Invariant

The digit function $\delta(r) = \lfloor br/p \rfloor$ sorts remainders into bins. Multiply every remainder by some fixed number $g$, and some of them change bins. Others stay put. The ones that stay are collisions: multiplication shuffled the room, but these didn't move.

At small primes, the bins are wide enough that every multiplier clears the room. No collisions, no matter what $g$ you choose. At larger primes, the bins crowd. Remainders start sharing. Most multipliers leave a few behind. But some multipliers still clear the room completely.

I wrote software to compute the collision count $C(g)$ for every multiplier at every prime, at any base. What I found surprised me.

## The gate width theorem

At every prime, in every base, exactly $b - 1$ multipliers produce zero collisions. I proved this, and the proof gives the exact list of which multipliers they are. Here is the computational verification at a few bases (the theorem covers all of them):

```
$ ./nfield verify gate-width

  base  3: 21 primes tested, gate width = 2  PASS
  base  7: 20 primes tested, gate width = 6  PASS
  base 10: 20 primes tested, gate width = 9  PASS
  base 12: 20 primes tested, gate width = 11  PASS
  base 16: 19 primes tested, gate width = 15  PASS
```

Nine multipliers clear the room in base 10. Six in base 7. Fifteen in base 16. The count depends on the base and nothing else. Not the prime. Not the size of the prime. Not where it sits among the other primes. Just the base.

It comes from one observation: multiplying every remainder by the base itself ($r \mapsto br \bmod p$) transforms the digit bins from contiguous intervals into residue classes modulo $b$. The geometry linearizes. In the new coordinates, the collision condition becomes a congruence, and a squeezing argument pins down exactly which multipliers satisfy it.

They form an explicit family:

$$g = -u/(b-u) \bmod p \quad \text{for } u = 1, \ldots, b-1$$

Rational numbers, reduced modulo the prime. They pair naturally under $u \mapsto b - u$. For even bases, $g = -1$ (the complement multiplier) is always one of them.

```
$ ./nfield verify mobius-family

  base  7: formula matches observed  PASS
  base 10: formula matches observed  PASS
  base 12: formula matches observed  PASS
```

The formula is proved for all primes and all bases. The verification confirms it computationally.

## The collision invariant

Fix the multiplier at $g = b$ and let the prime vary. Each prime gets a collision count. Subtract the expected count:

$$S(p) = C(b \bmod p) - \lfloor(p-1)/b\rfloor$$

I call this signed number the collision invariant. It measures how much a prime's digit structure deviates from average, and it is the central object of this paper and the series that follows.

I computed $S(p)$ for thousands of primes. The values jumped around, positive and negative, with no obvious pattern. Then I sorted by the last two digits:

```
$ ./nfield verify finite-det

  base 10, mod 100: 40 classes, all determined  PASS
    class  01: S(101) = S(401) = 0
    class  03: S(103) = S(503) = 2
    class  09: S(109) = S(409) = 8
    class  07: S(107) = S(307) = 0
```

Every prime ending in 01 gives $S = 0$. Every prime ending in 09 gives $S = 8$. It does not matter how large the prime is. Two digits determine the collision invariant completely.

This is the *finite determination theorem*: the collision invariant depends only on $p \bmod b^2$. The infinity of primes collapses onto a finite, deterministic structure. This fact has become the center of my research program.

## The periodic table

At every base, the collision invariant fills a finite table. In base 10 it has 40 entries. In base 3 it has 6. In base 7 it has 42. One signed integer per coprime class. Every prime maps to exactly one entry.

The tables are not random. At every base, the entries pair under the complement map $a \mapsto b^2 - a$:

$$S(a) + S(b^2 - a) = -1$$

In base 10: the class ending in 09 and the class ending in 91 sum to $-1$. The class ending in 03 and the class ending in 97 sum to $-1$. In base 3: every pair sums to $-1$. In base 7: every pair sums to $-1$. The architecture is universal.

```
$ ./nfield verify antisymmetry

  base  3: S(a)+S(m-a) = -1  PASS
  base  5: S(a)+S(m-a) = -1  PASS
  base  7: S(a)+S(m-a) = -1  PASS
  base 10: S(a)+S(m-a) = -1  PASS
```

The mean across every table is exactly $-1/2$. Positive on one side, negative on the other, organized by a single involution. This structure is *the same at every base*.

I had started with a counting question about long division. I now had a finite, signed, structured table attached to every base, encoding the collision behavior of every prime. The digit function $\lfloor br/p \rfloor$, which is taught in elementary school and then mostly forgotten, had produced a periodic table of the primes.

The collision invariant's Fourier transform carries L-function special values, and its centered sum over primes cancels at the boundary where the prime number theorem lives. Those results are in the [companion papers](https://arxiv.org/search/?query=petty+collision&searchtype=all). This paper proves the foundation: the architecture exists.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Collision Invariant](https://arxiv.org/abs/2604.00045)

*Alexander S. Petty*
March 2026
.:.

