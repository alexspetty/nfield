# Bin Derangements and the Gate Width Theorem

Pick a prime $p$ and a base $b$. Each residue $r$ from $1$ to $p - 1$ has a leading digit, determined by $\lfloor br/p \rfloor$. Residues that share a leading digit live in the same bin. Now multiply every residue by some nonzero $g$ modulo $p$. Some multipliers move every residue into a different bin. Others leave a few stuck.

At $p = 13$ in base $10$, the twelve residues split into ten bins. Eight bins hold one residue. Bin 3 holds residues 4 and 5 (both $4/13$ and $5/13$ start with digit 3). Bin 6 holds 8 and 9. Those crowded bins are where collisions happen.

Try every multiplier from 2 to 12 and count how many residues stay in their original bin:

```
 g     collisions   deranging?
--    -----------   ----------
 2          0           yes
 3          0           yes
 4          0           yes
 5          0           yes
 6          2           no
 7          0           yes
 8          0           yes
 9          0           yes
10          0           yes
11          2           no
12          0           yes
```

Nine zeros. The two non-deranging multipliers are $g = 6$ and $g = 11$, where residues get stuck in the crowded bins. Every other multiplier moves every residue to a new bin.

Nine at $p = 13$. Nine at $p = 29$. Nine at $p = 83$. Nine at $p = 1009$. The prime grows, the number of multipliers grows with it, but the count of deranging ones stays at nine. In base 7, it would be six. In base 3, two. Always $b - 1$.

![The nine deranging multipliers at five primes](https://alexpetty.com/content/images/2026/04/post11_derangements.png)

The gold dots are the deranging multipliers at five different primes. Their positions move. Their count does not.

## The change of variables

The proof works because the bins become simpler after one substitution.

The bins defined by $\delta(r)$ are contiguous intervals in the residue line. Intervals are awkward objects to move multiplicatively. The key step in the paper is to replace the residue $r$ by

$$x \equiv br \pmod p.$$

Under this permutation, the intervals turn into residue classes modulo $b$.

That is the whole trick. A geometric problem about intervals becomes an algebraic problem about congruence classes.

Once the problem is in that form, the bin-deranging condition can be written as a single congruence question. The answer comes from a short squeeze argument, and the deranging multipliers are given explicitly by

$$g \equiv -\frac{u}{b-u} \pmod p,\qquad u=1,\dots,b-1.$$

So the theorem does not just count the derangements. It writes them down.

## Dropping the primitive-root hypothesis

The earlier autocorrelation papers were strongest in the primitive-root case. There the multiplicative orbit of the base already gives a clean coordinate system. This paper drops that dependence completely.

The proof works directly on the digit function. No primitive-root hypothesis is needed. That means the theorem applies at every prime past the base, not just at the primes where the base generates the full multiplicative group.

That is a real shift in the program. One of the structural counts is now unconditional in the prime.

## The second result

The paper does more than count the zero-collision multipliers. It also gives an exact formula for the average collision count over the remaining multipliers.

Write

$$p-1=bQ+R,$$

where $Q=\lfloor (p-1)/b\rfloor$ and $R=(p-1)\bmod b$.

Then the mean collision count over the constructive multipliers is

$$\overline{C}=\frac{Q\bigl(b(Q-1)+2R\bigr)}{b(Q-1)+R}.$$

This formula has two clean special cases:

- if $R=0$, then $\overline{C}=Q$
- if $Q=1$, then $\overline{C}=2$

So the paper splits the behavior into two independent pieces:

- the base controls how many multipliers give zero collisions
- the prime controls how large the nonzero collision counts are on average

The second figure shows how well the mean formula fits the computed data.

![Mean collision count: observed vs formula](https://alexpetty.com/content/images/2026/04/post11_mean_formula.png)

Every prime past the base lands on the diagonal.

## Two controls

That is the real shape of the paper.

The base contributes a universal count, $b-1$.

The prime contributes the internal distribution of the surviving collisions.

Those two pieces are cleanly separated. The proof of the first goes through the conjugation trick. The formula for the second comes from a sum rule over the bins and the division $p-1=bQ+R$.

The base fixes the width of the gate. The prime fills in what happens beyond it.

---
## A note from 2026

*April 2026*

The change of variables $r \mapsto br \pmod p$ became a prototype. It turns interval geometry into residue-class algebra, and versions of the same move keep reappearing in the collision papers.

The theorem also dropped the primitive-root condition entirely. One of the recurring counts is now unconditional in the prime.

[The Collision Invariant](https://alexpetty.com/the-collision-invariant/) builds on exactly that kind of universality. The finite table at conductor $b^2$ still separates what the base controls from what the prime controls, only at a finer resolution.

The mean formula also aged well. At the time it looked like a useful secondary identity. In hindsight it is one of the earliest places where an average over bin geometry settles into a clean exact expression, a pattern that returns in much deeper form in [The Collision Spectrum](https://alexpetty.com/the-collision-spectrum/).

.:.

---

## Try it yourself

The current CLI exposes the verification sweep directly:

```text
$ ./nfield verify

Gate Width Theorem
  base 10: 20 primes tested, gate width = 9  PASS

Mobius Family
  base 10: formula matches observed  PASS

Mean Collision Count
  p= 29 Q= 2 R= 8: actual=2.8889 predicted=2.8889  ok
  p= 53 Q= 5 R= 2: actual=5.2381 predicted=5.2381  ok
  p= 61 Q= 6 R= 0: actual=6.0000 predicted=6.0000  ok
```

And the field data behind the theorem is still concrete:

```text
$ ./nfield field 13
$ ./nfield field 29
$ ./nfield field 53
```

Those three primes already show the two ingredients the paper tracks: changing bin geometry from prime to prime, and a deranging count that does not move.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Bin Derangements and the Gate Width Theorem](https://github.com/alexspetty/nfield/blob/main/research/bin_derangements.pdf)

---

*Alexander S. Petty*
July 2022 (updated April 2026)
.:.
