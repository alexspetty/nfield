# The Collision Transform and the Critical Strip

The [centered collision sum](https://alexpetty.com/the-centered-collision-sum/) converges at s = 1, the boundary where the prime number theorem lives. I proved that by decomposing the sum over Dirichlet characters and using Mertens' theorem to close the convergence. The proof was clean and short.

But $s = 1$ is the edge. Below it lies the critical strip, the region between $s = 0$ and $s = 1$ where the zeros of $L$-functions live, and where the Riemann Hypothesis makes its claim. The natural thing to do, once you have convergence at the edge, is to push the sum downward and see how far it survives.

![Edge and depth](https://alexpetty.com/content/images/2026/04/post17_edge_and_depth.png)

## Below the edge

The centered collision sum $F^\circ(s)$ is a weighted sum over primes. At $s = 1$, each prime contributes its centered deviation divided by $p$. At $s = 0.9$, the division is by $p^{0.9}$, which gives larger primes slightly more weight. At $s = 0.8$, more weight still. The further below $s = 1$ you go, the louder the large primes become, and the harder it is for the sum to stay bounded.

Here is what happens across five bases:

```
  s      base 3    base 5    base 7    base 10   base 12
-----    ------    ------    ------    -------   -------
 1.0     -0.151    -0.187    -0.137    -0.199    -0.278
 0.9     -0.168    -0.230    -0.186    -0.282    -0.417
 0.8     -0.186    -0.277    -0.250    -0.402    -0.624
 0.7     -0.205    -0.322    -0.337    -0.577    -0.926
 0.6     -0.227    -0.347    -0.457    -0.835    -1.346
 0.5     -0.257    -0.312    -0.636    -1.219    -1.880
```

Read down each column. At $s = 1.0$ the values are small and stable (the Centered Collision PNT, proved). As $s$ decreases, the values grow. The question is whether they *stabilize* at each new value of $s$, or whether they drift as you add more primes.

I measured the drift by splitting the prime range in half and comparing:

```
  s      base 3    base 5    base 7    base 10   base 12
-----    ------    ------    ------    -------   -------
 1.0     0.000     0.000     0.000     0.000     0.000
 0.9     0.000     0.001     0.001     0.000     0.001
 0.8     0.000     0.004     0.002     0.001     0.005
 0.7     0.000     0.013     0.007     0.004     0.017
 0.6     0.001     0.042     0.027     0.016     0.058
 0.5     0.003     0.135     0.099     0.065     0.205
```

Drift near zero means the sum is converging. Drift growing means it is not.

## Base 3 reaches the critical line

Look at the base-$3$ column. The drift is $0.003$ at $s = 0.5$. Essentially zero. The centered collision sum in base $3$ appears to converge all the way down to $s = 1/2$.

$s = 1/2$ is the critical line, the vertical line in the complex plane where the Riemann Hypothesis places the nontrivial zeros of $L$-functions. If the centered collision sum converges at $s = 1/2$, it is reaching the place where the deepest conjecture in mathematics makes its prediction.

The other bases do not reach as far. Base $5$ is stable to $s = 0.7$ but shows drift at $s = 0.6$. Bases $7$ and $10$ are similar. Base $12$ starts drifting at $s = 0.7$. The depth varies with the base.

![Penetration below s = 1](https://alexpetty.com/content/images/2026/04/penetration_depth.png)

## The base as instrument

Nobody thinks the base matters. We use base $10$ because we have ten fingers. Computers use base $2$ because switches have two states. Programmers use base $16$ because each hex digit maps to exactly four bits, turning a byte into two readable symbols instead of eight. The Babylonians chose base $60$ so that halves, thirds, quarters, fifths, sixths, tenths, and twelfths all come out clean, turning division into something you could do without writing anything down. In every case the base was picked to fit the job, and the mathematics is supposed to be the same regardless. The base is bookkeeping. It is the frame, not the painting.

In the collision transform, the base affects the depth of convergence.

Base $3$ has six Dirichlet characters in its collision transform. Base $12$ has forty-eight. That is not a notational difference. Each character contributes its own sum over primes, and each of those sums needs enough primes to settle down before you can see whether the whole thing converges. Six sums settle faster than forty-eight. That is why base $3$ reaches $s = 0.5$ in my data and base $12$ reaches only $s = 0.7$. The base sets how finely the transform can resolve the structure underneath, the way the aperture of a telescope determines how much light you need before you can see a faint star. A small base is a wide aperture. A large base is a narrow one. Same star. Different exposure time.

And that last sentence is important, because the $L$-functions do not know what base you are working in. Their zeros sit where they sit. The base does not change the structure; it changes the computational threshold at which the structure becomes visible. I believe the structure is the same in every base, and small bases reach the critical line with fewer primes because they have less noise to burn through before the signal comes clear.

## Under GRH

The collision transform writes $F^\circ(s)$ as a finite sum of terms, each involving $\log L(s, \chi)$ for an odd Dirichlet $L$-function. The even characters contribute nothing (the antisymmetry kills them, as in [the centered collision sum](https://alexpetty.com/the-centered-collision-sum/)). Only the odd $L$-functions matter.

If the Generalized Riemann Hypothesis is true, meaning every odd $L$-function modulo $b^{\ell+1}$ has its nontrivial zeros on the line $\text{Re}(s) = 1/2$, then $F^\circ(s)$ converges for every real $s > 1/2$. The collision sum reaches the critical line in every base.

That is a conditional statement, not a theorem. But the data in the tables above is consistent with it. Base $3$ appears to reach $s = 0.5$ already at the computational range I tested. The other bases appear to be converging more slowly toward the same depth, limited only by the number of primes in the computation.

**Conjecture.** *For every base $b$ and lag $\ell$, the penetration depth of the centered collision sum is $\sigma_0 = 1/2$. The collision transform reaches the critical line in every base.*

## Removing the mod-3 structure destroys convergence below $s = 1$

The centered collision deviation has a mod-$3$ structure. Primes congruent to $1 \pmod 3$ carry a different average centered deviation than primes congruent to $2 \pmod 3$. This asymmetry is subtle but persistent, and it is invariant under reweighting of bases.

I tried removing it. I subtracted the mod-$3$ bias on top of the spectral-class centering, producing a "doubly centered" sum $F^{\circ\circ}$.

At $s = 1$, the tested doubly centered sum remains bounded. But in the computations below $s = 1$, it grows rapidly.

In the table below, $F^\circ$ is the centered sum: the raw collision deviations with the per-family bias removed. $F^{\circ\circ}$ is the doubly centered sum: the same thing with the mod-$3$ bias removed on top of that. One correction deep, and two corrections deep.

```
  s      F° (centered)    F°° (doubly centered)
-----    -------------    ---------------------
 1.0          0.08              0.77
 0.7          0.27              12.3
 0.5          0.46              111
```

The centered sum $F^\circ$ stays bounded at $s = 0.5$. The doubly centered sum $F^{\circ\circ}$ grows rapidly.

![Removing the mod-3 structure](https://alexpetty.com/content/images/2026/04/post17_mod3_removal.png)

In the tested data, the mod-$3$ structure appears relevant to penetration below $s = 1$, even though it does not appear to control the same $s = 1$ cancellation.

This is an observed feature of the computations, not a theorem. But it suggests that the penetration of the collision transform into the critical strip depends on an interaction between the bilateral symmetry and the mod-$3$ distribution of collision coefficients. If that suggestion holds up, the depth of penetration is governed by both structures together.
## A note from 2026

*April 2026*

The contact with the critical strip turned out to be real.

The conditional penetration result (convergence below $s = 1$ given a zero-free hypothesis) became a central theorem of [The Collision Transform](https://arxiv.org/abs/2604.00047) preprint. The odd-character restriction (even characters vanish from the centered transform) became the antisymmetry theorem in the same preprint. Both results from this research note survived into the formal publication essentially unchanged.

The "base as instrument" framing from this paper also held up. The penetration depth is genuinely base-dependent at finite computation, and the convergence to universal depth $\sigma_0 = 1/2$ under GRH is the formal conjecture in the preprint. The observation that base $3$ reaches the critical line first, because it has the fewest characters, turned out to be structurally important: base $3$ is the simplest nontrivial case, and several later arguments were first tested and proved there before being generalized.

The mod-$3$ polarity discovery, the observation that removing the mod-$3$ bias appears to destroy penetration, became the seed of the neutrality theorem and eventually the general neutrality framework. The doubly-centered sum $F^{\circ\circ}$ that grew rapidly below $s = 1$ was the negative result that pointed me toward where to look next: not at the class means, not at the spectral-class structure, but at the mod-$3$ distribution of collision coefficients. The later papers are where that suggestion was tested and developed.

.:.

---

## Try it yourself

Run the centered collision sum in base $3$ and watch what happens as $s$ drops from $1.0$ toward $0.5$. The values grow, but they stabilize. In the tested range, the sum appears to converge all the way down to the critical line.

```
$ ./nfield penetration 3 --lag 1
```

Now run the same thing in base $12$. Same structure, but forty-eight characters instead of six. The sum stabilizes at $s = 1.0$ and $s = 0.9$, but starts drifting around $s = 0.7$. It looks like you are watching the instrument run out of resolution.

```
$ ./nfield penetration 12 --lag 1
```

Now the experiment that surprised me. Remove the mod-$3$ bias and run it again. Convergence at $s = 1$ survives. Below $s = 1$, the sum explodes. In the tested data, the mod-$3$ structure appears to be holding everything together.

```
$ ./nfield penetration 3 --lag 1 --double-center
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Collision Transform and the Critical Strip](https://github.com/alexspetty/nfield/blob/main/research/collision_transform_strip.pdf)

---

*Alexander S. Petty*
January 2024 (updated April 2026)
.:.
