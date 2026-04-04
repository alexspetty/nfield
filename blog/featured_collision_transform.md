# The Collision Transform

The collision invariant assigns a signed integer to every coprime class modulo $b^2$. In base 10, that means modulo 100: forty integers. Some positive, some negative, locked in complement pairs:

```
class 01: S =  0     class 99: S = -1     (sum = -1)
class 03: S =  2     class 97: S = -3     (sum = -1)
class 09: S =  8     class 91: S = -9     (sum = -1)
```

A signed pattern on a finite table. Look at it and a question forms: is it organized or is it noise? Does it have a dominant frequency, or does the energy spread evenly across the table?

There is a standard way to ask this. Decompose the pattern into Dirichlet characters, the natural frequencies of the group. Each character extracts one mode. The collection of modes is the collision transform.

When I computed it, two things happened that I did not expect. Both are proved in the paper.

## The silence

Half the frequencies are dead.

The collision invariant satisfies $S(a) + S(b^2 - a) = 0$. The complement map flips the sign. This acts like clamping a vibrating string at both ends; only certain vibration patterns are compatible. A string clamped at both ends cannot vibrate in even harmonics. The nodes fall in the wrong places. Only the odd harmonics survive.

Dirichlet characters come in two parities. Even characters satisfy $\chi(-1) = +1$. Odd characters satisfy $\chi(-1) = -1$. The complement antisymmetry kills every even character's contribution to the collision transform. Completely. Not approximately, not in the limit. The coefficient is exactly zero.

In base 10, there are 40 coprime classes modulo 100. The character group has 40 frequencies. Twenty are even. Twenty are odd. The collision invariant is inaudible at twenty frequencies. It speaks only in the odd half of the spectrum.

I did not build this in. The digit function $\lfloor br/p \rfloor$ has no obvious parity. The complement involution creates it. I call this the *antisymmetry theorem*: the pairing $r \mapsto p - r$ reaches up through the collision count and silences half the Fourier spectrum.

## The cancellation

Each prime carries a centered collision value $S(p)$. Some are positive, some negative. The question is whether they accumulate or cancel when you add them up across all primes.

Euler showed in 1737 that $\sum 1/p$ diverges: the primes, though sparse, are heavy enough that their reciprocals blow up. So if the collision values were all positive, the sum $\sum S(p)/p$ would diverge too. The primes would carry the collision signal to infinity.

But the values are not all positive. They oscillate. The antisymmetry forces positive classes and negative classes to coexist, and when you add $S(p)/p$ across primes, the positive terms and the negative terms wash each other out.

I computed the partial sums. They wander, dipping negative, climbing positive, but the swings shrink. The sum settles. At $s = 1$, it converges:

<div>
$$F(s) = \sum_{p} \frac{S(p)}{p^s}$$
</div>

This is the boundary where the prime number theorem lives. The classical PNT is equivalent to the Mobius function cancelling at this same boundary: $\sum \mu(n)/n$ converges. The collision invariant cancels here too, with a different function, for a different reason.

I did not expect this. The collision invariant counts bin coincidences. Nothing in its definition suggests it should know about primes, let alone cancel across them at the exact boundary that governs their distribution. But the decomposition into odd characters connects the collision sum to the same character sums that drive the PNT. The cancellation is inherited. The digit function taps into the prime number theorem without knowing it exists.

## Below the boundary

At $s < 1$: unconditional convergence is no longer guaranteed. The cancellation at $s = 1$ is the tightest the collision invariant can manage without further hypotheses.

Under stronger assumptions about the L-functions attached to the odd characters, the convergence extends deeper. The collision sum continues to cancel below $s = 1$, conditional on how far the L-function zeros stay from the real axis. The digit function does not see those zeros directly, but its Fourier spectrum is tuned to the same frequencies. The convergence of the collision sum and the location of the zeros are linked through the character decomposition.

## The prime 3, again

There is a third surprise, and it connects back to where this program began.

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

The balanced family is the neutral center. I call this the *neutrality theorem*.

Why 3? Because $10 \equiv 1 \pmod{3}$. The base carries the prime 3 in its residue structure, and the collision table inherits that structure as a three-way split. The prime 3 appeared in the [first paper of this series](https://github.com/alexspetty/nfield/blob/main/research/golden_ratio_selects_prime_three.pdf) as the golden ratio's algebraic selection. Here it appears again, organizing the collision spectrum into three families with a neutral center. The digit function remembers this prime at every level of its architecture.

The complement symmetry silences half the spectrum. The surviving frequencies cancel across primes at the same boundary where the prime number theorem lives. And the prime 3, the one the golden ratio selected, organizes the surviving structure into three families with a neutral center at exactly $-1/2$. Silence, cancellation, and structure; each one a consequence of the one before it, each one coming from the same floor function that produces digits during long division.

All of it from $\lfloor br/p \rfloor$. A floor function, sorting remainders into bins. It should not reach this far into the theory of primes. It does.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Collision Transform](https://arxiv.org/abs/2604.00047)

*Alexander S. Petty*
March 2026
.:.

