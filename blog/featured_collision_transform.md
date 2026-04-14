# The Collision Transform

Take the [collision periodic table](https://alexpetty.com/the-collision-periodic-table/). Forty signed integers in base $10$, computed from long division. To the eye they look irregular. Positives and negatives scattered across the cells, no obvious pattern.

This paper takes the table apart with one tool, the Fourier transform, and finds three sharp symmetries hiding inside it. All three come from a single observation about the table itself. Complement pairs sum to $-1$.

```
class 01: S =  0     class 99: S = -1     (sum = -1)
class 03: S =  2     class 97: S = -3     (sum = -1)
class 09: S =  8     class 91: S = -9     (sum = -1)
```

Forty cells, twenty pairs, every pair sums to $-1$, no exceptions. From that one fact, three theorems unspool.

## The first symmetry: half the spectrum is silent

A finite table is a signal. Signals can be decomposed into frequencies. The natural frequencies for a table modulo $b^2$ are Dirichlet characters; the decomposition is a Fourier transform. The collection of Fourier coefficients is the *collision transform*.

Now apply the transform to the collision table and watch what happens.

The first thing you notice is the constant. The very first Fourier coefficient, the one corresponding to the trivial character, captures the table's overall mean. Compute it directly and it comes out to exactly $-1/2$. Not approximately. The number $-1/2$, exactly. This is the same $-1/2$ the previous post highlighted: the global mean of the forty integers is the trivial Fourier coefficient, and it sits at a clean rational.

The second thing you notice is what comes next. You compute coefficient after coefficient and half of them are zero. Every other one. **Half the frequencies of the collision table are silent.**

Half the frequencies. Not approximately, not in the limit. Exactly half. The coefficient corresponding to every *even* Dirichlet character vanishes. The coefficient corresponding to every *odd* Dirichlet character does not.

Here is why. The complement antisymmetry, $S(a) + S(b^2 - a) = -1$ for every coprime $a$, acts on the table the way clamping acts on a vibrating string. A string clamped at both ends cannot vibrate in even harmonics; the nodes fall in the wrong places. Only the odd harmonics survive. Dirichlet characters split exactly the same way: the even ones satisfy $\chi(-1) = +1$ and respect the complement, the odd ones satisfy $\chi(-1) = -1$ and fight it. The complement antisymmetry kills every even character's contribution to the Fourier transform. Completely.

In base 10, the character group has 40 frequencies. Twenty are even. Twenty are odd. The collision invariant is inaudible at twenty frequencies. It speaks only in the odd half of the spectrum.

I did not build this in. The digit function $\lfloor br/p \rfloor$ has no obvious parity. The complement involution creates one. I call this the *antisymmetry theorem*. The pairing $r \mapsto p - r$ reaches up through the collision count and silences half the Fourier spectrum.

## The second symmetry: cancellation at the prime number theorem boundary

So the centered collision invariant is built from twenty surviving frequencies. The next question is what those twenty frequencies do when you sum across all primes.

Each prime $p$ contributes a centered collision value $S(p)$ to the running total. Some are positive, some negative. The natural way to sum them is the harmonic series weighted by collision values:

<div>
$$F(s) = \sum_{p} \frac{S(p)}{p^s}$$
</div>

The exponent $s$ controls how aggressively the smaller primes count. At $s = 1$, the weights are $1/p$, the same weights Euler used in 1737 to prove that the primes are heavy enough to make $\sum 1/p$ diverge. So if the collision values were all positive, $F(1)$ would diverge too. The collision signal would carry off to infinity.

But the values are not all positive. The antisymmetry forces positive cells and negative cells to coexist, and the question becomes whether the positive contributions and the negative contributions wash each other out across the population of primes.

They do. Here is the mechanism. After the antisymmetry theorem, the collision sum is a finite linear combination of objects called *prime character sums*:

<div>
$$\sum_p \frac{\chi(p)}{p}, \qquad \chi \text{ odd modulo } b^2$$
</div>

Each one of these is a classical object. Mertens proved in 1874 that the prime sum inside any single residue class modulo $m$ behaves like $(\log\log x)/\phi(m)$ plus a constant plus a small error. When you weight the residue classes by an odd character $\chi$, the character coefficients cancel the divergent $\log\log x$ piece, and what remains converges. Each individual character gives a convergent prime sum at $s = 1$. The collision sum is a finite combination of those, so it converges too.

Substitute back. The harmonic-weighted sum of collision values across primes converges:

<div>
$$F(1) = \sum_p \frac{S(p)}{p} \quad \text{converges}$$
</div>

This is the boundary where the prime number theorem lives. The classical PNT is equivalent to the Möbius function cancelling at this same boundary, that is, $\sum \mu(n)/n$ converges. The collision invariant cancels here too, with a different function, for a different reason. But it cancels at the exact boundary. The digit function taps into the prime number theorem without knowing it exists.

## Reaching below the boundary

Convergence at $s = 1$ asks little of any single prime: the weight $1/p$ decays fast. Lowering the exponent below $s = 1$ makes each prime count more loudly, and forces the cancellation to be more delicate. At $s < 1$, the collision sum is no longer guaranteed to converge unconditionally. Whether it does depends on the L-functions attached to those twenty surviving odd characters.

There is a precise theorem about this. Suppose every odd L-function modulo $b^2$ has no zeros above some line $\operatorname{Re}(s) = \sigma_0$. Then the collision sum $F(s)$ converges for every real $s > \sigma_0$. Reducing $\sigma_0$ pushes the cancellation deeper into the strip. The depth at which the collision sum converges equals the depth at which the L-functions stay zero-free.

Computation says the cancellation reaches well below $s = 1$ in practice:

```
$ ./nfield collision_sum --bases 3,7,10,12 --s 1.0,0.8,0.6,0.5

   s     base 3    base 7    base 10    base 12
  1.0    -0.15     -0.14      -0.20      -0.28
  0.8    -0.19     -0.25      -0.40      -0.62
  0.6    -0.23     -0.46      -0.84      -1.35
  0.5    -0.26     -0.64      -1.22      -1.88
```

Across 348,488 primes, $F(s)$ stays bounded down to $s = 0.5$ in base 10 and at least that far in the other tested bases. The signal continues to cancel at depths where unconditional theorems no longer apply.

A small extra observation has a poetic shape. The Fourier coefficients of the collision invariant are *negatively correlated* with the magnitudes of the prime character sums most sensitive to L-function zeros. The Pearson correlation is about $-0.25$ across all tested prime bases. Said in plain language: the collision invariant places its largest Fourier weight on exactly those characters whose L-functions are the best behaved. The digit function appears to listen, preferentially, to the well-behaved L-functions and ignore the trouble spots. Nothing in its definition suggests it should know which L-functions are well-behaved. It does anyway.

## The third symmetry: a neutral family at the prime 3

Go back to the table. Take each class number and ask: what is it modulo 3?

```
class 01:  01 mod 3 = 1     S =  0
class 03:  03 mod 3 = 0     S =  2
class 09:  09 mod 3 = 0     S =  8
  ...
class 91:  91 mod 3 = 1     S = -9
class 97:  97 mod 3 = 1     S = -3
class 99:  99 mod 3 = 0     S = -1
```

Group all forty classes by this value and average the collision values within each group:

```
mod 3 = 0:  mean S = +0.29   (tilts positive)
mod 3 = 1:  mean S = -1.29   (tilts negative)
mod 3 = 2:  mean S = -0.50   (exactly -1/2)
```

Two groups tilt. One group sits at exactly $-1/2$, the grand mean. Perfectly neutral.

The reason the third group sits at $-1/2$ is short and beautiful. The complement reflection $a \mapsto 100 - a$ permutes the residue classes modulo 3. Two of the three classes get swapped with each other. One class is fixed. Inside the fixed class, the reflection pairs each unit with another unit *in the same class*, and the antisymmetry $S(a) + S(100 - a) = -1$ forces every such pair to average to $-1/2$. The fixed class inherits the global mean exactly.

I call this the *neutrality theorem*. There is always a balanced family. It is the family the complement reflection holds still.

Why mod $3$ specifically? Because $10 \equiv 1 \pmod 3$. The base carries the prime $3$ in its residue structure, and the collision table inherits that structure as a three-way split. The prime $3$ also appeared in [the golden ratio selects prime three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/), where the algebraic selection that the golden ratio performs on the small primes lands on $3$ for the same residue reason. Here it appears again, organizing the collision spectrum into three families with one neutral center. The digit function remembers this prime at every level of its architecture.

## The aggregate is empty

One small extra observation, this one negative. Compute the collision invariant in many bases at once and sum the values across bases with a fixed weighting. The aggregate signal vanishes. Individual bases can produce $F(s)$ values ranging from $-1.4$ to $+5.1$, but a weighted sum across bases lands at $-0.01$. The collision invariant's structural content is *base-specific*. Each base sees a different view of the primes. The views do not aggregate into a single universal view; they cancel out.

That is unusual. Most signals in number theory either persist or strengthen when you average across viewpoints. The collision invariant's content disappears under averaging. This means each base is doing its own real work, not contributing to a shared average. The base is a lens, and the lens matters.

## Three theorems, one observation

The complement antisymmetry silences half the Fourier spectrum. The surviving frequencies cancel across primes at the same boundary where the prime number theorem lives. The mod-3 reflection holds one residue class fixed, and that class inherits the global mean exactly.

Silence. Cancellation. A neutral family.

Each is a consequence of one observation: complement pairs sum to $-1$. Each falls out of the antisymmetry of the table by a different route through Fourier analysis. Each one was already in the table when long division put it there.

All of it from $\lfloor br/p \rfloor$. A floor function, sorting remainders into bins. It should not reach this far into the theory of primes. It does.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Preprint: [The Collision Transform](https://arxiv.org/abs/2604.00047)

*Alexander S. Petty*
March 2026
.:.
