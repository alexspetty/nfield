# The Spectral Power of the Digit Function

Take a prime $p$ in base $10$. For each residue $r = 1, \ldots, p-1$, look at the leading digit of $r/p$. Group the residues by that digit. The sizes of those ten groups are the **bucket sizes** of the prime, and they determine far more than you would expect from a list of ten integers.

At $p = 7$, the bucket sizes are

```text
(0,1,1,0,1,1,0,1,1,0)
```

Six buckets contain one residue, and four are empty.

At $p = 13$, the bucket sizes are

```text
(1,1,1,2,1,1,2,1,1,1)
```

Eight buckets are singletons, and two contain two residues.

At $p = 29$, the bucket sizes are a mix of $2$s and $3$s.

![Bucket sizes of the digit function](https://alexpetty.com/content/images/2026/04/spectral_power_buckets.png)

These lists look simple, but they already control several things:

- the alignment limit
- the digit-partitioning condition
- part of the later spectral structure

Here that information is gathered into a single function on the frequencies of the prime. I call it the **spectral power** of the digit function.

## From buckets to frequencies

The key fact is elementary. Each bucket is a run of consecutive residues.

That happens because the digit function $\delta(r)=\lfloor 10r/p \rfloor$ is monotone in $r$. As $r$ increases, the leading digit can only stay the same for a while and then move up by one. So the residues assigned to digit $0$ form an interval, the residues assigned to digit $1$ form the next interval, and so on.

Intervals are easy to analyze with Fourier series. The Fourier transform of a consecutive run is a classical trigonometric object called a **Dirichlet kernel**. So each bucket contributes one Dirichlet kernel, determined only by the size of that bucket.

The spectral power $\Phi$ is what you get by taking those bucket Fourier coefficients, squaring their magnitudes, and summing over the ten buckets. It is a nonnegative function of the frequency.

That is the whole construction.

## The zeroth mode

One frequency is special: frequency $0$.

At frequency $0$, Fourier analysis just counts. A bucket of size $n_d$ contributes $n_d$, and after squaring and summing we get

$$\Phi(0) = n_0^2 + n_1^2 + \cdots + n_9^2.$$

This is exactly the old bin-sum from [The Alignment Limit](https://alexpetty.com/the-alignment-limit-for-all-primes/).

So the alignment limit did not disappear. It became the lowest mode of a larger object.

The first gain is structural. The spectral power does not replace the earlier invariant. It contains it.

## A worked example: $p = 13$

For $p = 13$, the buckets are

```text
digit 0:  {1}
digit 1:  {2}
digit 2:  {3}
digit 3:  {4,5}
digit 4:  {6}
digit 5:  {7}
digit 6:  {8,9}
digit 7:  {10}
digit 8:  {11}
digit 9:  {12}
```

There are eight singleton buckets and two doubled buckets.

At frequency $0$, this gives

$$\Phi(0) = 8 \cdot 1^2 + 2 \cdot 2^2 = 16.$$

That is the same bin-sum we already knew.

Away from frequency $0$, the singleton buckets are simple: each contributes the same flat amount at every frequency. The doubled buckets are the only source of variation. They create a low, slow envelope in the graph of $\Phi$: large near the lowest frequencies, smaller near the middle, then rising again by symmetry.

So for $p = 13$, almost all of the shape comes from just two doubled buckets.

This is a good example of what the spectral power does. It turns a small combinatorial imbalance in the buckets into a global frequency profile.

![Spectral power of the digit function](https://alexpetty.com/content/images/2026/04/spectral_power_phi.png)

At $p = 11$, every occupied bucket is a singleton, so the graph is flat. At $p = 13$, two doubled buckets create a visible envelope. At $p = 29$, the bucket sizes vary more, and the graph has genuine frequency structure.

## Three layers

The spectral power organizes several earlier facts.

First, it recovers the alignment limit through the identity

$$\Phi(0) = S(p,10).$$

Second, it gives a clean characterization of digit-partitioning primes. A prime is digit-partitioning exactly when every occupied bucket has size $1$. In that case, every bucket contributes the same flat amount at every frequency, so $\Phi$ is constant. Conversely, if $\Phi$ is constant, the buckets must all be singletons. So:

- digit-partitioning
- all occupied buckets of size $1$
- flat spectral power

are three ways of saying the same thing.

This is the second reason the paper matters. A condition first defined in terms of decimal collisions can also be recognized spectrally.

## The limit of $\Phi$ alone

The spectral power keeps magnitudes. It throws away phase.

That means it does **not** determine everything. In particular, it does not yet determine the eigenvalue spectrum from [The Spectral Structure of Fractional Fields](https://alexpetty.com/the-spectral-structure-of-fractional-fields/). To recover that, you need a richer object that remembers how the Fourier modes line up with one another, not just how large they are.

The spectral story does not end here. What appears in this paper is the magnitude side of it.

That is still a real gain. A prime's bucket sizes no longer sit there as a list of ten integers. They now define a whole frequency profile, with the alignment limit at one end and flatness of digit-partitioning at the other.

---
## A note from 2026

*April 2026*

This paper gives the first full frequency-space portrait of the digit function. Before it, the bucket data had been compressed into a few scalars. Here the whole partition is pushed into Fourier space at once.

That shift matters because [The Autocorrelation Formula](https://alexpetty.com/the-autocorrelation-formula/) needs more than one scalar summary, and [Phase-Filtered Ramanujan Sums and the Spectral Gate](https://alexpetty.com/phase-filtered-ramanujan-sums-and-the-spectral-gate/) studies what happens when the same harmonic data is filtered by residue-class structure. [The Collision Spectrum](https://alexpetty.com/the-collision-spectrum/) uses the same interval geometry again in a different arithmetic setting.

The common fact behind all of these papers is simple and sturdy: the digit buckets are consecutive runs of residues. Once that is written down, classical harmonic analysis becomes available.

.:.

---

## Try it yourself

```text
$ ./nfield spectral 11
  bucket sizes: 1,1,1,1,1,1,1,1,1,1
  Phi(0) = 10
  Phi flat at every frequency

$ ./nfield spectral 13
  bucket sizes: 1,1,1,2,1,1,2,1,1,1
  Phi(0) = 16
  two doubled buckets create a low-frequency envelope

$ ./nfield spectral 29
  bucket sizes: a mix of 2s and 3s
  Phi(0) = 80
  the spectrum has visible variation across the frequencies
```

What changes from one prime to the next is not just the total at frequency $0$. The whole shape changes with the bucket sizes.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Spectral Power of the Digit Function](https://github.com/alexspetty/nfield/blob/main/research/spectral_power.pdf)

---

*Alexander S. Petty*
October 2021 (updated April 2026)
.:.
