# The Centered Collision Sum

In [the collision fluctuation sum](https://alexpetty.com/the-collision-fluctuation-sum/) I added up the collision deviations across primes and watched the total drift downward without limit. Then I subtracted the per-family biases and the drift stopped. The raw sum diverges. The centered sum converges.

That was a numerical observation. This paper proves it.

## Finite determination, generalized

The proof rests on a generalization of the *finite determination theorem* from [the collision invariant](https://alexpetty.com/the-collision-invariant/). That paper showed that the collision deviation at lag one depends only on the prime's last two digits in base ten, collapsing the infinity of primes onto a table of forty entries. The [collision periodic table](https://alexpetty.com/the-collision-periodic-table/) is that table.

What I found here is that finite determination extends to every lag, and the modulus grows with it. At lag one, the deviation depends on $p \bmod 100$ (the last two digits). At lag two, $p \bmod 1000$ (the last three). At lag three, $p \bmod 10{,}000$ (the last four). At lag $\ell$, the modulus is $b^{\ell+1}$, and the deviation is a function on the finite group of units modulo that number. The principle is the same at every lag. Only the resolution changes.

This is what makes the convergence proof possible. A function on a finite group has a Fourier transform. And a Fourier transform can be taken apart character by character.

## The class means become exact

Once the deviation is a function of the last two digits, the per-family biases from [the collision fluctuation sum](https://alexpetty.com/the-collision-fluctuation-sum/) stop being estimates and become computable. Average the forty table entries within each spectral class (primes ending in $1$, primes ending in $3$, primes ending in $7$, primes ending in $9$) and the class means come out as exact rational numbers:

```
last digit     class mean     computed (664K primes)
----------     ----------     ----------------------
  1 (R=0)       -17/10               -1.709
  3 (R=2)        -9/10               -0.897
  7 (R=6)        -1/10               -0.097
  9 (R=8)        +7/10               +0.699
```

The computed values, running across $664{,}574$ primes, match the exact rational values to three significant figures. The grand mean across all four classes is exactly $-1/2$. The complementary pairs sum to exactly $-1$: $(-17/10) + (7/10) = -1$, $(-9/10) + (-1/10) = -1$. Every pair, every base.

![Twenty antisymmetric pairs](https://alexpetty.com/content/images/2026/04/class_means_antisymmetry.png)

For prime bases, evaluating the table reveals something even more striking. The class means are evenly spaced. In base $3$ they are $-2/3$ and $-1/3$. In base $7$ they run from $-6/7$ to $-1/7$ in steps of $1/7$. The pattern is consistent with the formula $\overline{S}_R = (R+1)/b - 1$, verified by direct computation at every prime base I have tested. Whether a structural proof of this formula exists is an open question. The even spacing is observed, not explained.

## The proof

Now the convergence, and I can say it quickly because the finite determination does all the work.

The collision deviation $S(p)$ is a function of $p \bmod 100$. A function on a finite group can be expanded over the Dirichlet characters of that group, the way a periodic signal can be expanded in sines and cosines. The expansion has one term per character. The trivial character (the one that assigns the value $1$ to every class) carries the grand mean of the function, which is $-1/2$. That $-1/2$ is the source of the Mertens drift. Centering removes it.

Every remaining character, every non-trivial character, produces a prime sum $\sum \chi(p)/p$ that converges. This is a classical result. Mertens proved in 1874 that the prime harmonic series $\sum 1/p$ grows like $\log \log x$. When you weight it by a non-trivial character, the $\log \log x$ growth cancels (because the character values sum to zero over the residue classes), and what remains is finite.

The centered sum is a finite combination of these convergent character sums. A finite sum of convergent sums converges. Done.

The details live in the [paper accompanying this writing](https://github.com/alexspetty/nfield/blob/main/research/centered_collision_sum.pdf). The architecture is what I just described. I call the result the *Centered Collision PNT*, by analogy with the classical prime number theorem, which encodes the same kind of cancellation at the same boundary $s = 1$.

## Watching it converge

```
primes        raw sum       centered sum
------        --------      ------------
  1,000        -1.46            0.020
 10,000        -1.69            0.023
100,000        -1.86            0.023
664,574        -1.99            0.023
```

The raw sum drifts. The centered sum sits at $0.023$ and does not move. The entire Mertens drift lived inside four rational numbers, the class means. Subtract them and the drift vanishes.

![Centering removes the drift](https://alexpetty.com/content/images/2026/04/centered_vs_raw.png)

The stability holds across every base and lag I have tested:

```
base    lag    raw sum     centered sum
----    ---    -------     ------------
  3      1      -1.59          0.163
  7      1      -1.66          0.031
 10      1      -1.76          0.043
 10      2      -1.83          0.072
 10      3      -0.56         -0.227
 12      1      -1.67          0.129
```

Six tests. Four bases. Three lags. Every raw sum drifts. Every centered sum is stable. The convergence is not an artifact of base ten.

The class mean $-2/3$ in base $3$ at $R = 0$ is the same constant the [golden ratio selected](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) as the alignment limit of the prime $3$, and the same constant that appeared as a [per-family collision bias](https://alexpetty.com/the-collision-fluctuation-sum/) in base $10$. The centering that makes the collision sum converge is the centering that removes it.
## A note from 2026

*April 2026*

Looking at this paper now, the Centered Collision PNT turned out to be the structural backbone of my first three publications:

- [The Collision Invariant](https://arxiv.org/abs/2604.00045) (arXiv, March 2026). Gate width theorem, finite determination, reflection identity, half-group theorem.
- [The Collision Transform](https://arxiv.org/abs/2604.00047) (arXiv, March 2026). Antisymmetry, centered convergence at $s = 1$, conditional penetration below $s = 1$.
- [The Collision Spectrum](https://arxiv.org/abs/2604.00054) (arXiv, March 2026). Decomposition theorem, L-value encoding, Parseval moment identity.

The proof here, short as it is, contains all three of the key moves that those preprints develop in full: finite determination collapses the population of primes onto a finite group, the collision transform decomposes the centered deviation over Dirichlet characters, and Mertens' theorem closes the convergence.

The finite determination theorem became the foundation of the [collision periodic table](https://alexpetty.com/the-collision-periodic-table/). The forty-cell table, the antisymmetry, the gate width theorem at depth two, all rest on the fact that $S(p)$ is a function of $p \bmod b^2$. Without finite determination, there is no table. Without the table, there is no transform. Without the transform, there is no decomposition theorem and no L-value extraction. The whole analytical tower sits on this one combinatorial fact about the digit function.

The class mean formula for prime bases, $\overline{S}_R = (R+1)/b - 1$, has not been generalized to a closed form for composite bases. In base $10$, the class means are rational numbers satisfying the reflection symmetry and grand mean $-1/2$, but no single-formula expression for them is known. Whether one exists is still open.

.:.

---

## Try it yourself

The first command computes the raw and centered fluctuation sums side by side. Watch the raw sum grow as you increase the prime count. Watch the centered sum stay put.

```
$ ./nfield centered_sum 10 --lag 1 --primes 100000
```

The second command prints the class means for each spectral family. The values should come out as exact rationals. Check that each complementary pair sums to $-1$ and that the grand mean is $-1/2$.

```
$ ./nfield class_means 10 --lag 1
```

The third command is the one that shows finite determination in action. Pick any two primes that end in the same two digits and verify they produce the same collision deviation. Try $109$ and $50{,}009$. Try $191$ and $99{,}991$. Try any pair you like. They will agree.

```
$ ./nfield finite_det 10 --lag 1
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Centered Collision Sum](https://github.com/alexspetty/nfield/blob/main/research/centered_collision_sum.pdf)

---

*Alexander S. Petty*
October 2023 (updated April 2026)
.:.
