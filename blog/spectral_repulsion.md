# The Spectral Repulsion

I knew the collision invariant and the prime distribution were avoiding each other in the data. [The double transversality](https://alexpetty.com/the-double-transversality/) showed it qualitatively, the way you can see two magnets pushing apart without measuring the force. But "they avoid each other" is not a number. I wanted the number.

Three questions.

1. How much avoidance is there?
2. Is it the same at every base?
3. Does it have consequences beyond the collision transform, for other problems about primes?

Three answers.

1. About forty percent of the random-relabeling overlap is missing in the tested bases.
2. The ratio is strikingly stable across the tested bases.
3. Yes, it has consequences in the computations.

## Measuring the gap

Imagine a room full of chairs. Two people walk in with fixed seating preferences, but before they sit you randomly relabel the chairs for one of them. If you repeat this many times, you can measure the average overlap between where they end up. That is the null model here: fixed weights, random channel correspondence. If the measured overlap is consistently smaller than that random-relabeling baseline, there is repulsion.

I did this with the collision spectrum and the prime spectrum. The collision invariant distributes its weight across the frequency channels, putting more on some channels and less on others. The prime distribution does the same. I normalized both so each one sums to $1$, making them proper probability distributions on the same set of channels. Then I measured their pointwise overlap.

If you hold both distributions fixed and randomly permute the channel labels of one of them, the expected overlap is $1/n$. That is true no matter how nonuniform the two distributions are. For spectra that systematically under-overlap relative to that random-relabeling baseline, the overlap is less.

```
base    channels    overlap     relabel 1/n    ratio
----    --------    -------     -----------    -----
  3         3       0.1931        0.3333        0.58
  5        10       0.0766        0.1000        0.77
  7        21       0.0257        0.0476        0.54
 11        55       0.0108        0.0182        0.60
 13        78       0.0078        0.0128        0.61
 17       136       0.0041        0.0074        0.56
 19       171       0.0046        0.0058        0.79
 23       253       0.0024        0.0040        0.60
 29       406       0.0015        0.0025        0.63
 31       465       0.0013        0.0022        0.63
 37       666       0.0009        0.0015        0.58
```

The last column is the one that matters. If the measured overlap matched the random-relabeling baseline, it would read $1.0$ at every row. If the spectra were perfectly orthogonal, sharing no channels at all, it would read $0$.

It reads about $0.6$. At every tested base. From $3$ channels to $666$.

The collision spectrum and the prime spectrum share only about sixty percent of the overlap predicted by the random-relabeling baseline. The other forty percent is missing. The two spectra are not merely unrelated by that benchmark; they systematically under-overlap, and the strength of that under-overlap is remarkably stable across the tested channel counts.

I call that missing forty percent the spectral repulsion.

## The number that does not move

The repulsion ratio is remarkably stable. From $3$ channels to $666$ channels, across eleven bases, it hovers near $0.6$. The values range from $0.54$ to $0.79$, but the central tendency does not drift. It does not approach $1$ (the random-relabeling baseline) as the base grows. It does not collapse toward $0$ (perfect orthogonality). It sits near $0.6$ and holds.

That stability is the finding. A number that depends strongly on the base would be a curiosity. A number that stays this stable across the tested bases looks structural. It suggests the collision transform has a fixed relationship to the prime distribution, a fixed angle of avoidance, that does not vary much with the digit system. The base changes the characters, the modulus, the number of channels, everything about the setup. The fraction of overlap that survives changes surprisingly little.

I do not know what $0.6$ is. Whether it has a closed form or is simply an empirical constant is an open question. What I know is that it is stable everywhere I can measure it, and a number that stable usually has a reason.

## Spotlight and floodlight

So the two spectra under-overlap the random-relabeling baseline by about forty percent, and they do it in a remarkably similar way across the tested bases. I wanted to understand the geometry of the avoidance. Not just how much, but how. If two people avoid each other in a building, there are different ways they could do it. They could take turns using the same rooms. Or one could live in a closet while the other roams the whole floor. 

It is the second one.

I measured the effective support of each distribution, the number of channels that carry most of its weight. A distribution concentrated on a few channels has small effective support. A distribution spread across many channels has large effective support.

```
base    channels    collision support    prime support
----    --------    -----------------    -------------
  3         3              2.0                2.5
  7        21              7.0               10.7
 13        78             18.0               52.0
 19       171             33.2              112
 29       406             64.0              295
```

At base $29$, the collision invariant puts most of its weight on $64$ channels out of $406$. The prime distribution fills $295$ of them. As the base grows, the collision spectrum stays narrow while the prime spectrum expands. The spotlight does not widen. The floodlight does. The gap between them grows.

That is the geometry behind the $0.6$. The collision invariant lives in a small corner of the channel space. The prime distribution fills most of the room. They overlap where the corner meets the room, and that overlap is about sixty percent of the random-relabeling baseline. The forty percent that is missing is not being destroyed by some later mechanism. It was never there in the first place. The collision invariant was born in a corner. The primes were born everywhere else.

## Multiplication only

The spectral repulsion tells you the collision invariant avoids certain channels. But which channels? The answer reveals something fundamental about what the collision invariant is.

The channels it suppresses appear to be the channels that carry additive information about primes. The channels that matter for questions like "which primes add up to which even numbers." I tested this directly. For each even number $N$, I took every pair of primes $p + q = N$, multiplied their collision deviations together, and added up the products. If the collision invariant had a strong additive preference, this sum would carry a sustained signal.

```
base    mean H/R     std H/R
----    --------     -------
  3     +0.000        0.63
  5     +0.001        0.89
  7     +0.002        1.20
 10     +0.002        1.55
 13     +0.004        1.75
```

Near zero. At every tested base. The collision invariant appears largely blind to the additive structure of primes in this experiment. It sees how primes interact with the digit function through multiplication. It has little visible purchase on how primes combine through addition. The spectral repulsion is consistent with that separation.

This is a characterization of the instrument suggested by the data. The collision invariant is a purely multiplicative object. The additive landscape is nearly invisible to it in the tested range, not because the landscape is empty, but because the instrument is not built to detect it. An optical telescope cannot pick up radio waves. The blindness is in the instrument, not in the sky.

## The reflection underneath

Every result in this program traces back to one identity. $S(a) + S(m-a) = -1$. The reflection. It created the neutrality theorem. It killed the Mertens term. It drove the centered convergence. And here it is again.

If one prime has a non-negative collision deviation, its reflection partner must have $-1$ or worse. They cannot both be non-negative. For primes that sum to an even number divisible by $m$, the two primes *are* reflection partners. So both members of that additive pair cannot sit in the positive half of the collision table. The bilateral symmetry forces opposite signs across the additive divide.

The obstruction is partial. It covers $1/m$ of all even numbers, not all of them. But the principle does not care about coverage. The reflection is always there, at every scale, at every modulus, pairing every unit with its complement and forcing their deviations to sum to $-1$. The collision invariant was forged by this symmetry. The partial obstruction does not explain the full additive blindness observed in the data, but it shows that the reflection is working against additive concentration at a structural level.

One identity. The neutrality, the convergence, the partial Goldbach obstruction. The reflection keeps appearing at different levels of the same structure. I did not design this. I followed the digit function where it led, and the same room kept opening up.

## A note from 2026

*April 2026*

The ratio $\rho \approx 0.6$ turned out to be one of the most stable numerical invariants in the program. In the tested range, it does not depend much on the base or the number of channels. Whether it has a closed form remains open.

The additive near-blindness was not something I went looking for. It fell out of the spectral repulsion. The collision invariant suppresses the channels that seem to carry additive information, so the collision-weighted additive correlation stays near zero in the tested range. That result clarified what the collision transform is: a multiplicative instrument, structurally close to perpendicular to addition.

The spotlight-and-floodlight picture (collision concentrates, primes spread) became the starting point for [the collision spectrum and the L-function landscape](https://alexpetty.com/the-collision-spectrum-and-the-l-function-landscape/). The concentration turns out to be a consequence of the Bernoulli-diagonal factorization: the collision coefficients are products of an arithmetic factor and a geometric factor, and the arithmetic factor dominates, pulling the weight onto a few channels.

.:.

---

## Try it yourself

**Measure the repulsion.** Compute the spectral overlap at each prime base. The last column should land near $0.6$ throughout the tested range, from $3$ channels to $666$. The avoidance ratio is strikingly stable across the tested bases.

```
$ ./nfield spectral_overlap --lag 1 --bmax 37
```

**See the shape.** Compare the effective supports. The collision spectrum should concentrate on far fewer channels than the prime spectrum, and the gap should widen as the base grows. Spotlight next to floodlight.

```
$ ./nfield effective_support --lag 1 --bmax 37
```

**Test the additive near-blindness.** Goldbach's conjecture says every even number is the sum of two primes. Run the collision-weighted correlation across those pairs for even numbers from $1{,}000$ to $100{,}000$. The mean should stay near zero. The most famous additive question about primes, and the collision invariant has very little to say about it in this computation.

```
$ ./nfield goldbach_null 10 --lag 1 --nmin 1000 --nmax 100000
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Spectral Repulsion](https://github.com/alexspetty/nfield/blob/main/research/spectral_repulsion.pdf)

---

*Alexander S. Petty*
January 2025 (updated April 2026)
.:.
