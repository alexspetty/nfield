# Phase-Filtered Ramanujan Sums and the Spectral Gate

The last digit of a prime looks like the least interesting thing about it. It is not.

Take the repeating blocks of $1/p$ for a few small primes:

```text
$ ./nfield field 7
  1/7 => 0.|142857| (closed)

$ ./nfield field 13
  1/13 => 0.|076923| (closed)

$ ./nfield field 53
  1/53 => 0.|0188679245283| (closed)
```

The loops are different, as they should be. The central question in the paper is not the loops themselves but how they respond to shifting.

For a given prime, shift the repetend by one place, then by two, then by three, and count how many digit positions still agree with the original. Those counts are the autocorrelation values.

At some shifts the count is zero. At others it is not. The striking thing is that the vanishing shifts are not scattered at random. In the primitive-root computations behind the paper, they appear in a fixed count depending only on the base, while the pattern of the nonzero shifts is organized by the residue class of the prime modulo the base.

That is the first point of this paper: the last digit of a prime in base $10$ is already sorting the primes into spectral families.

## Four families in base ten

For primes greater than $5$, the last digit can only be $1$, $3$, $7$, or $9$. The paper shows that these four residue classes are not just decimal trivia. They determine the continued-fraction tail of $p/10$, and that tail determines the coarse bin geometry of the prime.

Here is the full table in base $10$:

![The four continued-fraction tails of base 10](https://alexpetty.com/content/images/2026/04/four_family_tails.png)

- primes ending in $1$ have tail $[10]$ and uniform bins
- primes ending in $3$ have tail $[3,3]$ and two large bins
- primes ending in $7$ have tail $[1,2,3]$ and six large bins
- primes ending in $9$ have tail $[1,9]$ and eight large bins

So the continued fraction of $p/10$ is not an ornament. It is a compact way of recording the same coarse geometry that later shows up in the autocorrelation data.

That part is theorem-level in the paper: the spectral classes are exactly the coprime residue classes modulo the base, so base $10$ has four of them, base $12$ has four, base $30$ has eight, and in general the count is $\varphi(b)$.

## The gate

The second point is more empirical.

In the primitive-root computations, the nontrivial shifts split into two kinds:

- shifts where the autocorrelation vanishes exactly
- shifts where it stays bounded away from zero

The paper packages this into a phase filter $\Gamma(\ell)$. It measures how much of the underlying harmonic contribution survives at shift $\ell$.

For the examples studied in the note, the filter behaves like a gate. A shift is either blocked entirely or it passes with a definite amount of signal. There is no smooth middle fade.

The term **spectral gate** is useful because it names that dichotomy directly. The point is not that the prime has one global “strength.” The point is that certain shifts are admitted and others are suppressed.

The observed width of that gate in base $10$ is $9$, one less than the base. The figure below shows the pattern across primes up to $500$.

![Gate width vs loop length](https://alexpetty.com/content/images/2026/04/gate_vs_loop.png)

When the loop length is shorter than $9$, every nontrivial shift can be swallowed by the gate and the autocorrelation vanishes away from shift $0$. When the loop is longer, room opens up for nonzero structure.

This is an observation in the paper, not a proved universal theorem. The note is careful about that status.

## The Ramanujan connection

The autocorrelation formula from [The Autocorrelation Formula](https://alexpetty.com/the-autocorrelation-formula/) writes the self-match count as a weighted sum over additive characters. Classical Ramanujan sums are built from the same kind of ingredients, but with uniform weights.

The new feature here is the filter. The weights are no longer uniform. They are shaped by the cross-spectral data of the digit bins and by the multiplicative orbit of the base.

That is what the phrase **phase-filtered Ramanujan sum** means in this paper:

- Ramanujan-type because the sum is still over the same harmonic world
- filtered because only certain phase alignments survive

This does not turn the autocorrelation into a classical Ramanujan sum. It puts it next to one, with the digit-bin geometry supplying the nonuniform weight.

## The role of the last digit

The last digit does not determine the whole autocorrelation profile. It does determine the coarse family the prime belongs to.

That distinction matters.

At $p = 13$ and $p = 53$, the last digit is the same, so the continued-fraction tail is the same and the coarse family is the same. But the loop lengths are different, the fine placement of the surviving shifts is different, and the full autocorrelation data is different.

So the family controls the broad shape, not every detail.

That is exactly the level where the paper is strongest. It does not pretend to classify every shift at every prime. It shows that the coarse gate structure is already visible in the residue class of the prime modulo the base, and that the continued fraction of $p/b$ is one clean way to read it.

---
## A note from 2026

*April 2026*

The language of “spectral gate” was a way of naming a real pattern before the later collision papers supplied a better framework for it.

[The Collision Invariant](https://alexpetty.com/the-collision-invariant/) and [The Collision Spectrum](https://alexpetty.com/the-collision-spectrum/) eventually replace the continued-fraction viewpoint with a cleaner Fourier and character-theoretic one. But the family structure seen here survives that translation. The last-digit classes in base $10$ become the first visible layer of a deeper residue-class organization.

That is one reason the paper still matters. It isolates one of the first places where a coarse residue class begins to act like a structural fingerprint rather than a superficial label.

It also captures a real transition in the program. Up through [The Autocorrelation Formula](https://alexpetty.com/the-autocorrelation-formula/), the spectral story is still being assembled one object at a time. Here the residue classes start to behave like named families. From this point on, classification by arithmetic type becomes part of the basic grammar of the work.

.:.

---

## Try it yourself

Look at two primes in the same family and compare them to a prime from a different one.

```text
$ ./nfield field 13
$ ./nfield field 53
$ ./nfield field 29
```

The primes $13$ and $53$ share the same last digit, so they lie in the same coarse family. The prime $29$ lies in a different one.

Now inspect the magnitude-side data for one of them:

```text
$ ./nfield spectral 29
  Phi(0) = 80
  Autocorrelation R(ell): values 0, 2, and 4 appear away from the origin
```

The spectral data is no longer flat, and the autocorrelation is no longer trivial. That is the regime where the gate picture starts to matter.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Phase-Filtered Ramanujan Sums and the Spectral Gate](https://github.com/alexspetty/nfield/blob/main/research/phase_filtered_ramanujan.pdf)

---

*Alexander S. Petty*
April 2022 (updated April 2026)
.:.
