# The Autocorrelation Formula

One quantity in the spectral chain resisted a closed form longer than the others.

Take the repeating block of $1/7$ in base $10$:

```text
142857
```

Shift it by one place and compare the shifted copy with the original:

```text
1 4 2 8 5 7
4 2 8 5 7 1
```

There are no matches. Shift by two, three, four, or five places, and the answer is still zero. For $p = 7$, the repeating block never agrees with a nontrivial cyclic shift of itself.

That behavior is not typical. At $p = 29$, some shifts produce matches. At $p = 97$, the profile is much richer.

![Autocorrelation profiles](https://alexpetty.com/content/images/2026/04/autocorrelation_profile.png)

The number of matches at shift $\ell$ is the **autocorrelation** $R(\ell)$. It is one of the key objects in the spectral side of the program, because the eigenvalues of the cross-alignment matrix are the discrete Fourier transform of this profile.

The problem was simple to state and awkward to compute. The definition of $R(\ell)$ comes straight from digit comparison, but that means computing it directly requires writing out the repetend and checking every shift by hand or by brute force.

Here that quantity is expressed directly in terms of the prime's harmonic data.

## The limit of spectral power alone

[The Spectral Power of the Digit Function](https://alexpetty.com/the-spectral-power-of-the-digit-function/) already gave a closed formula for the magnitude profile of the digit partition. That was enough to recover the bin-sum and to characterize digit-partitioning primes, but it was not enough to recover $R(\ell)$.

The reason is the same as in ordinary wave interference. Magnitude tells you how large a frequency component is. It does not tell you how two frequency components line up when they are added. For that, phase matters.

Autocorrelation depends on exactly that missing phase information. Two frequencies can have the same magnitude and still reinforce or cancel in different ways depending on how they are aligned.

So a one-variable magnitude function is not enough. A two-variable object is needed.

## The cross-spectral table

The repair is to keep track of pairs of frequencies instead of single frequencies.

For each pair $(k,k')$, the paper defines a table $G(k,k')$ built from the Fourier coefficients of the digit bins. The diagonal of this table recovers the spectral power. The off-diagonal entries record the phase relations that the spectral power discards.

That is the right level of information for autocorrelation.

One fact about this table drives the whole argument:

$$\sum_{k,k'} G(k,k') = 0.$$

At first sight this looks incidental. It is not. It is the cancellation identity that turns a long expansion into a usable formula.

## The formula

The starting point is the direct definition of $R(\ell)$: count the residues whose digit agrees with the digit of their shifted partner.

The agreement test can be written in terms of the digit bins. Each bin indicator can then be expanded in additive characters on $\mathbf{Z}/p\mathbf{Z}$. After that substitution, the residue sum collapses and the result becomes a sum over pairs of frequencies weighted by the cross-spectral table $G$.

At that stage there are two classes of terms:

- terms where the combined frequency is zero
- terms where it is not

The standard character sum over nonzero residues takes two values in those two cases, so the formula splits into two pieces. The cancellation identity

$$\sum_{k,k'} G(k,k') = 0$$

then forces those two pieces to collapse into one.

What remains is the autocorrelation formula:

$$R(\ell) = \frac{1}{p}\sum_{k=0}^{p-1} G\!\left(k,\,-k\,b^{-\ell}\!\!\!\pmod p\right).$$

So $R(\ell)$ is no longer defined by comparing digits in a loop. It is computed by walking one orbit path through the table $G$ and summing what lies on that path.

That is the structural step this paper contributes.

## Watching it work at $p = 7$

At $p = 7$, every occupied digit bin has size one. The table $G$ takes only two values: $6$ on the diagonal (where $k = k'$) and $-1$ everywhere else. A $7 \times 7$ grid, bright along the diagonal, dark in every other cell.

![The table at p = 7 with shift-1 path](https://alexpetty.com/content/images/2026/04/autocorrelation_table_walk.png)

The gold circles mark the path for shift 1. Each shift determines its own path through the table: the formula sends frequency $k$ to $k \cdot b^{-1} \bmod p$. Since $10 \equiv 3 \pmod{7}$, shift 1 maps $k$ to $3k \bmod 7$, and the path visits cells $(0,0)$, $(1,3)$, $(2,6)$, $(3,2)$, $(4,5)$, $(5,1)$, $(6,4)$. Seven cells. One of them lands on the diagonal and picks up $6$. The other six land off the diagonal and each picks up $-1$.

$$6 + 6(-1) = 0. \qquad R(1) = 0/7 = 0.$$

Shifts 2 through 5 trace different paths through the same table, but each one also hits the diagonal exactly once. Every path sums to zero. The formula reproduces the full row of zeros from the opening without ever writing down the repetend.

This is the point where the chain closes:

- the digit bins determine the Fourier coefficients
- the Fourier coefficients determine the table $G$
- the table $G$ determines $R(\ell)$
- the discrete Fourier transform of $R(\ell)$ gives the eigenvalues

Everything is now explicit.

## The hole that remains

The clean formula belongs to the primitive-root case, where the base runs through the full multiplicative orbit modulo $p$. In that setting, the path through $G$ has the right shape and the cancellation identity finishes the job.

At multi-coset primes, the same expansion can still be written down, but the collapse is no longer so direct. The table is there, the paths are there, but the orbit structure is smaller and the neat one-line reduction no longer follows from the same argument.

So the paper does something precise. It closes the chain in the regime where the Fourier geometry is cleanest, and it identifies exactly what remains to be understood outside that regime.

That is still a substantial change in the state of the subject. Before this paper, autocorrelation was the one place in the chain where brute-force digit comparison was still doing essential work. After this paper, that role is gone in the primitive-root case.

---
## A note from 2026

*April 2026*

The cancellation identity behind this paper lasted. The same pattern keeps returning: a one-variable invariant sits on the diagonal of a richer two-variable object, and the off-diagonal data is what makes the stronger formula possible. [The Collision Spectrum](https://alexpetty.com/the-collision-spectrum/) has the same flavor. Variance-type quantities are visible on the diagonal, but the real structure lives in the correlations.

This paper also fixed something methodological. Once the autocorrelation formula was written down, the path from digit bins to eigenvalues became explicit from end to end. That set a standard the collision papers kept. Even when the analytic setting becomes much deeper, the quantities under study are still built from finite arithmetic data that can be checked directly in small cases.

.:.

---

## Try it yourself

```text
$ ./nfield autocorrelation 7
  R(0) = 6
  R(1) = R(2) = R(3) = R(4) = R(5) = 0

$ ./nfield autocorrelation 29
  R(0) = 28
  nonzero values appear at several shifts

$ ./nfield autocorrelation 97
  R(0) = 96
  the self-match profile is visibly structured
```

At $p = 7$, the nontrivial shifts all vanish. At $p = 29$, the profile is still sparse but no longer trivial. At $p = 97$, the pattern is dense enough that the underlying harmonic structure is hard to miss.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Autocorrelation Formula](https://github.com/alexspetty/nfield/blob/main/research/autocorrelation_formula.pdf)

---

*Alexander S. Petty*
January 2022 (updated April 2026)
.:.
