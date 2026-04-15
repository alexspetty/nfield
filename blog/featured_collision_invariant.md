# The Collision Invariant

Take a prime, any prime. Do long division by it in some base. The remainders fall into b bins, one bin per leading digit. This is the digit function, the floor of br/p, the long-division step that turns each remainder into the next digit of the expansion.

Now do something simple. Pick a multiplier $g$ from the units mod $p$. Multiply every remainder by $g$ and re-sort. Most remainders change bins. Some do not. The ones that do not are *collisions*; multiplication has shuffled the room, but these stayed put.

Count the collisions:

<div>
$$C(g) = \#\{r \in \{1, \ldots, p-1\} : \delta(r) = \delta(gr \bmod p)\}$$
</div>

That is the collision count. It depends on the prime, the base, and the multiplier. It is a function on the multiplicative group mod $p$, defined by an utterly elementary procedure. Nothing about it suggests it should have structure beyond what its definition imposes.

This paper proves four things about the collision count that should not be true.

**One.** The number of multipliers that produce zero collisions is always exactly $b - 1$. Not approximately. Not on average. Exactly $b - 1$, at every prime, in every base. The count depends on the base alone, not on the prime, not on its size, not on its location among the primes.

**Two.** The collision count's deviation from the average value is determined by the prime's last two base-$b$ digits. The infinity of primes collapses onto a finite table, one entry per coprime residue class modulo $b^2$.

**Three.** The entries of that finite table satisfy an exact reflection. Complementary pairs sum to $-1$, with no exceptions, in any base.

**Four.** Every "wrapping set" attached to the construction has exactly half the size of the unit group. Every one. Always.

Each of the four theorems is proved by the same single move applied four ways. That move is what the paper hangs on, so I will explain it before any of the theorems.

## The single move

The digit bins look like geometric objects. They are contiguous intervals on the integer line; the first bin is the residues from $1$ to $\lfloor (p-1)/b \rfloor$, the second is the next stretch, and so on. Geometric problems on integer intervals are hard to handle algebraically. The intervals do not respect multiplication; the boundaries between them depend on the prime; nothing about them suggests an algebraic identity.

There is one operation that converts the geometry into algebra. Multiply every residue by the base $b$, then reduce modulo $p$.

After this single operation the bins are no longer contiguous intervals. They are *residue classes modulo $b$*. The bin that used to be "the residues whose leading base-$b$ digit is 0" is now "the residues that are congruent to 0 modulo $b$." The bin that used to be the second interval is now the residues that are 1 mod $b$. And so on.

Geometry has become algebra. The question "which residues lie in the same digit interval?" has become "which residues are congruent modulo $b$?" The first question is hard. The second question is undergraduate.

I call this the *linearization*. After it, every theorem in the paper is a short algebraic argument. Without it, the same theorems would be hard counting problems on intervals. The linearization is what makes the architecture visible.

## One: the gate width is always $b - 1$

The first question I put to the linearization was the simplest one. Which multipliers $g$ move every residue out of its original bin?

After the substitution $r \mapsto br \bmod p$, the no-collision condition translates into a congruence on a small auxiliary integer $c = b/(1 - g) \bmod p$. Working through the algebra, the deranging multipliers turn out to form an explicit family of rational numbers, reduced modulo the prime:

<div>
$$g = -\frac{u}{b - u} \bmod p, \qquad u = 1, 2, \ldots, b - 1$$
</div>

There are exactly $b - 1$ of them. Always. The count is independent of the prime. The rational family $\{-u/(b-u) : u = 1, \ldots, b-1\}$ sits above the primes; only its reduction mod $p$ depends on which prime you chose.

I call this the *gate width theorem*. Across every base and every prime tested, the count comes out to $b - 1$:

```
$ ./nfield gate_width 3 7 10 12 16

  base  3:  21 primes scanned,  gate width = 2
  base  7:  20 primes scanned,  gate width = 6
  base 10:  20 primes scanned,  gate width = 9
  base 12:  20 primes scanned,  gate width = 11
  base 16:  19 primes scanned,  gate width = 15

  every base: gate width = b - 1 (no exceptions across the scan)
```

Nine deranging multipliers in base 10. Six in base 7. Fifteen in base 16. Always, forever, $b - 1$.

No primitive-root hypothesis. No algebraic constraint on the prime. Just $b - 1$ deranging multipliers, sitting in their rational family, every time.

The family pairs naturally under $u \mapsto b - u$. When $b$ is even, the involution has a fixed point at $u = b/2$, and the deranging multiplier $-1$ (the complement) is always one of them. Even bases always carry the complement among their deranging multipliers.

## Two: only the last two digits matter

Pick one multiplier and stare at it. The most natural choice is $g = b$ itself, the base. The collision count $C(b \bmod p)$ at this single multiplier has a specific deviation from the bin-size average, and the deviation is what I want a name for. Call it $S(p)$:

<div>
$$S(p) = C(b \bmod p) - \left\lfloor \frac{p-1}{b} \right\rfloor$$
</div>

I call this signed integer the *collision invariant*. It can be positive or negative. It measures how much the prime $p$'s digit structure deviates from the average prediction.

I computed $S(p)$ for thousands of primes. The values jumped around with no obvious pattern. Then I sorted the primes by their last two digits in base 10:

```
class 01:  S(101) = 0    S(401) = 0    S(701) = 0
class 03:  S(103) = 2    S(503) = 2    S(1303) = 2
class 09:  S(109) = 8    S(409) = 8    S(1009) = 8
class 91:  S(191) = -9   S(491) = -9   S(1091) = -9
```

Every prime ending in 01 gives $S = 0$. Every prime ending in 09 gives $S = 8$. Every prime ending in 91 gives $S = -9$. The size of the prime does not enter. Two digits determine the collision invariant completely.

I call this the *finite determination theorem*. The collision invariant depends only on $p \bmod b^2$. The infinity of primes collapses onto a finite, deterministic table.

The proof is the linearization once more. After multiplying by $b$, the collision count becomes a sum of contributions from a specific set of "slices" indexed by an integer in a finite range. The slice contributions depend only on $p \bmod b^2$, so the whole sum depends only on $p \bmod b^2$, so the collision invariant depends only on $p \bmod b^2$.

The number of entries in the table depends on the base. Six in base 3. Forty-two in base 7. Forty in base 10. Each entry corresponds to a residue class coprime to $b$, and every prime larger than $b^2$ maps to exactly one entry.

This is the architecture that [the collision periodic table](https://alexpetty.com/the-collision-periodic-table/) walks through cell by cell. The collision invariant is a finite, signed table. A *periodic table for primes*, attached to every base.

## Three: complement pairs sum to $-1$

Look at the table once more. Every entry has a partner. The partner of class $a$ is the complement $b^2 - a$. In base $10$, the partner of class $09$ is class $91$. The partner of class $03$ is class $97$. Twenty pairs in total, splitting the forty cells exactly in half.

Compute $S(a)$ and $S(b^2 - a)$ for any pair. They sum to $-1$. Every time.

```
class 09 + class 91:   +8 + (-9) = -1
class 03 + class 97:   +2 + (-3) = -1
class 17 + class 83:   +1 + (-2) = -1
```

I call this the *reflection identity*:

<div>
$$S(a) + S(b^2 - a) = -1$$
</div>

It is exact, and it has no exceptions, at every base. The proof is the linearization once more. Under the involution $a \mapsto m - a$ (where $m = b^2$), the slice contributions of $a$ and $m - a$ swap their wrapping behavior: where one slice wraps for $a$, the same slice does not wrap for $m - a$. The bookkeeping works out so every complement pair lands on $-1$.

A clean corollary: the average of the table over all units is exactly $-1/2$. The involution $a \mapsto m - a$ pairs up all the units, every pair averages to $-1/2$, so the overall average is $-1/2$. This is the $-1/2$ that runs through the whole research program. It comes from here.

## Four: every wrapping set is exactly half

The fourth theorem comes from looking inside the proof of the second one. The slice formula behind finite determination expresses $S(a)$ as a sum over a finite set of slices, where each slice answers a single binary question. Does this multiplication wrap past zero modulo $b^2$, or does it not?

The set of units $a$ for which slice $n$ wraps is called the *wrapping set* $W_n$. It is a subset of the unit group, and the natural question is how big it is.

Exactly half. For every non-trivial slice, exactly $\phi(b^2)/2$ units wrap and exactly $\phi(b^2)/2$ units do not. Without exception.

I call this the *half-group theorem*. The proof, once again, is the linearization-driven involution. The map $a \mapsto m - a$ sends "wraps" to "does not wrap" and vice versa, and it is a bijection on the unit group. So the wrapping set and its complement have equal size, and that size is exactly half.

The same complement involution that organizes the global structure of $S$ also organizes the local structure of every individual slice. One symmetry, four consequences.

## Four theorems, one observation

The gate width theorem says exactly $b - 1$ multipliers always derange the bins.

The finite determination theorem says the collision invariant is a finite table indexed by the prime's last two base-$b$ digits.

The reflection identity says the entries of the table pair under complementation and sum to $-1$.

The half-group theorem says every wrapping set is exactly half the unit group.

The collision invariant does not redefine what a prime is. It shows that once a base is fixed, a prime carries more visible structure than indivisibility alone suggests. The digit function of long division imposes a finite collision geometry on the prime, and that geometry is rigid enough to satisfy a reflection identity and a finite determination law. In that sense, the prime is not only an atomic integer. It is also a structured object in a base-dependent arithmetic space.

All four come from one observation: multiplying every remainder by the base flattens the digit bins into residue classes. After that single move, the geometric structure of long division becomes the algebraic structure of a finite group, and every theorem is a short calculation in that group.

The digit function $\lfloor br/p \rfloor$, the operation taught in third grade and then mostly forgotten, has produced a finite signed table attached to every base, organized by a complement involution, with gate counts and wrapping counts that depend on the base and nothing else. That table is the collision invariant.

The Fourier transform of the table carries L-function special values. Its centered sum over primes cancels at the boundary where the prime number theorem lives. Those results are in the [companion papers](https://arxiv.org/search/?query=petty+collision&searchtype=all). This paper proves the foundation: the architecture exists.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Preprint: [The Collision Invariant](https://arxiv.org/abs/2604.00045)

*Alexander S. Petty*
March 2026
.:.
