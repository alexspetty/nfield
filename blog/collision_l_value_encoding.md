# The Collision Spectrum and the L-Function Landscape

For five years I had been watching the collision invariant do things I could not explain. It avoided the zero-sensitive channels. It repelled the prime spectrum. It concentrated its weight on a small cluster while the primes spread across everything. I could measure the avoidance, quantify it, test it, scramble it, destroy it and rebuild it. I could not say why it happened.

Then the coefficients factored.

## The factorization

The collision invariant has Fourier coefficients, one for each odd Dirichlet character. I had been treating those coefficients as data points, measuring their correlations, watching their patterns. I had never asked what they were made of.

They are made of two things. For a primitive odd character $\chi$ modulo $b^2$ (with $b$ prime), the coefficient splits into a clean product of two factors. One is a generalized Bernoulli number, $B_{1,\bar\chi}$, a classical object studied since the 1700s. Through the Bernoulli--$L$-value formula, its magnitude is proportional to the $L$-function's value at $s = 1$. This is the analytic factor. It measures the character's health at the edge.

The other is a diagonal character sum, $S_G(\chi)$, built from the edges between the digit bins of $\lfloor br/p \rfloor$. This is the geometric factor. It measures how the character interacts with the digit boundaries.

The collision coefficient is their product. Not a correlation between them. Not a statistical relationship. The literal product.

![The collision spectrum at base 7: concentrated on few characters](https://alexpetty.com/content/images/2026/04/post22_factorization-1.png)

## From correlation to cause

The [anti-correlation](https://alexpetty.com/the-general-neutrality-theorem/) and the [spectral repulsion](https://alexpetty.com/the-spectral-repulsion/) observed that collision weights track $L$-values. Those were measurements. This factorization is the first exact structural reason for part of that behavior.

The $L$-value is not merely correlated with the collision coefficient. It is *inside* it. The Bernoulli factor sits in every coefficient as a multiplicative term. Characters near a zero have small Bernoulli factors, so they have small collision coefficients. That does not by itself prove the full anti-correlation picture, because the diagonal factor still matters. But it does show that edge data from $L(1,\chi)$ is structurally built into every collision coefficient.

## The digit function squares the $L$-value

At base $5$, the diagonal sum $|S_G(\chi)|$ turns out to be exactly proportional to $|L(1, \chi)|$ for every primitive odd character. Both factors encode the same $L$-value. The collision coefficient becomes

$$\vert\hat{S}^\circ(\chi)\vert \propto \vert L(1, \chi)\vert^2$$

The digit function squares the $L$-value. At base $5$, the collision spectrum is a perfect quadratic photograph of the $L$-function landscape.

At larger bases, the proportionality softens. The diagonal sum still correlates with $|L(1)|$, but the correlation decays. (Base 3 is omitted: it has only two primitive odd characters, too few for a meaningful correlation.)

```
base    chars    correlation    corr x log(base)
----    -----    -----------    ----------------
  5        8       1.00              1.61
  7       18       0.88              1.71
 13       72       0.83              2.13
 19      162       0.86              2.52
 31      450       0.84              2.90
 43      882       0.85              3.18
 61     1800       0.84              3.46
 71     2450       0.84              3.57
```

![Collision spectrum concentration across bases](https://alexpetty.com/content/images/2026/04/post22_correlation_decay-1.png)

Above $0.83$ out to base $71$ with $2{,}450$ characters. The last column drifts upward, suggesting decay on the scale of $c / \log b$. At base $5$ the encoding is quadratic. At large bases it approaches linear. The digit function still encodes $L$-values, but the fidelity fades.

## The signal and the noise

At base $5$ the encoding is perfect. At base $71$ it is still strong but not perfect. Something is diluting the signal as the base grows. I wanted to understand what.

The geometric factor can be broken into two pieces. One piece is the $L$-value itself, the signal. The other is a crowd of smaller terms that add up to something about the same size as the signal but pointed in a random direction. Call it the noise.

Imagine listening to a singer in an empty room. You hear every note clearly. That is a small base. Now put fifty other people in the room, all talking at once. The singer is still there, still the same volume, but the crowd noise makes it harder to pick out the melody. That is a large base.

At small bases, the crowd is small and erratic. The singer's voice stands out because it is the steadiest thing in the room. At large bases, the crowd is large and settled. The average volume stabilizes, and the singer's voice blends into the ambient level. The correlation fades.

The fading appears to happen on the scale of $c / \log b$. Slow. Logarithmically slow in the tested range. At base $71$ the correlation is still $0.84$. The singer never disappears in the data so far. You just need a better microphone.

## Digits and $L$-functions in the same equation

A consequence:

The [centered collision sum](https://alexpetty.com/the-centered-collision-sum/) converges at $s = 1$. That is a proved theorem about a sum over primes weighted by the digit function. Before the decomposition theorem, that was a statement about digits. After the decomposition theorem, it becomes a statement about $L$-functions.

The decomposition cracks the sum open. The primitive odd sector, the part controlled by the characters the decomposition theorem handles, expands into an exact sum of products. Each product contains an $L$-value (through the Bernoulli factor), a geometric weight (through the diagonal sum), and a prime character sum. The triangle inequality bounds the collision transform beneath this weighted sum of $L$-data. The bound goes one direction: $|F^\circ|$ is bounded above by the weighted moment, not the other way around. The digit function sits beneath the $L$-function landscape, not above it.

But even that one-directional bound says something. A sum built from integer division and floor functions is sitting in the same inequality as $L$-function special values. The digit function and the analytic landscape are in the same equation, linked by the Bernoulli factor.

At base $5$, where both factors encode $|L(1)|$, this becomes a weighted second-moment expression. Three things that have no obvious reason to be in the same equation, a digit function, $L$-values at the edge, and prime character sums, bound together in one inequality.

## Edge and depth

![Edge and depth](https://alexpetty.com/content/images/2026/04/post22_edge_depth.png)

Between $s = 0$ and $s = 1$ lies the critical strip, the region where the zeros of $L$-functions live and the Riemann Hypothesis makes its claim. The edge of the strip, $s = 1$, is familiar ground. The depth, approaching $s = 1/2$, is where the hardest questions hide.

Every $L$-function has a value at the edge of the strip, at $s = 1$. Think of it as a pulse. A strong pulse means the character is healthy at the edge. A faint pulse means a zero is sitting close to $s = 1$, pulling the value down. The Bernoulli factor is proportional to this pulse. It sits inside every collision coefficient, wired into the digit function's Fourier structure.

Now imagine an $L$-function with a zero deeper in the strip, away from the edge, closer to the critical line at $s = 1/2$. That zero makes $\log L(s, \chi)$ blow up. In the collision transform, the term for that character develops a singularity, a spike, a place where one piece of the sum tries to go to infinity.

Singularities are where the action is. They are the fingerprints the zeros leave on the transform.

And the size of each fingerprint is set by the pulse.

An $L$-function with a strong pulse leaves a deep, heavy fingerprint when it has a zero at depth. The collision transform feels it. An $L$-function with a faint pulse leaves a scratch. The zero is there, but the transform barely registers it.

To be precise about what is happening here. The collision invariant does not produce the singularities. It is a finite table of integers. Nothing in it blows up. The singularities come from $\log L(s, \chi)$ diverging near a zero, which is purely analytic machinery. But the decomposition theorem puts the collision coefficients directly in front of that machinery. The collision invariant controls the amplitude of each singularity, the volume at which each zero is heard. It is the audience, not the performer. But the factorization gives it the front row seat, and the Bernoulli factor determines which performers it hears loudest.

This raises a natural question. If the collision invariant has a front row seat to the zeros, why does it not deal with them directly?

Because the $B_1 = 0$ position is unoccupied. If an $L$-function had a zero exactly at the edge, $|L(1, \chi)| = 0$, the Bernoulli factor would vanish and the collision coefficient for that character would be exactly zero. The collision transform would not just suppress that character. It would be blind to it entirely. But by a classical theorem (essentially Dirichlet's), no $L$-function of a non-trivial character has a zero at $s = 1$. So $B_1 = 0$ never happens. The collision invariant lives in the neighborhood of that position, reading the gradient, never touching the point itself. Characters with zeros near the edge have faint coefficients. Characters with zeros far from the edge have strong ones. The collision invariant sees the zeros the way a seismometer on the coast sees earthquakes offshore. Not the fault line itself, but the wave that arrives at the shore.

I want to say that again, because it is the strangest thing in this program. The digit function $\lfloor br/p \rfloor$, built from integer division and floor functions, couples two different places in the critical strip. It connects what an $L$-function does at the boundary to what it does in the interior. It is listening to the edge, and the edge is reporting on the depth. The factorization says it does this exactly, by algebra.
## A note from 2026

*April 2026*

The decomposition theorem became the central result of [The Collision Spectrum](https://arxiv.org/abs/2604.00054) preprint. The factorization connects the collision program to classical analytic number theory. Everything before this was building the instrument. This is what was inside.

The seismometer metaphor turned out to be more than a metaphor. The polarity field measures the avoidance directly across the critical strip, and the zero-density theorem proves that the collision weights select for characters whose $L$-functions have no zeros near the edge. The Bernoulli factor is the mechanism in both cases. The decomposition theorem is the structural identity that makes those results possible.

The Apostol mechanism (packet magnitude, phase uniformity, variance decay) remained as computational observations. Proving the variance decay rate $c/\log b$ is an open problem. It would close the gap between the exact factorization and the observed correlation between $|S_G|$ and $|L(1)|$. A separate paper on the diagonal-Bernoulli identity develops the factorization further and explores the fourth-moment structure at base $5$.

The connection to class numbers was unexpected. For imaginary quadratic fields, the class number $h(-d)$ satisfies $h(-d) = (\sqrt{d}/\pi) |L(1, \chi_d)|$. At base $5$, the collision coefficient is proportional to $h(-d)^2$. The digit function squares class numbers. That observation makes the decomposition theorem feel less like a technical identity and more like a window into something deep about the relationship between digits and arithmetic.

.:.

---

## Try it yourself

This is the paper where the collision program stops being about digits and starts being about $L$-functions. These three commands show you the transition.

**First, verify the factorization.** Pick a prime base. The code will compute every collision coefficient, every Bernoulli factor, and every diagonal sum. Multiply the Bernoulli factor by the diagonal sum, divide by $\phi(b^2)$, and compare to the collision coefficient. They should agree to machine precision. That is not a correlation. That is an identity. The collision coefficient *is* that product.

```
$ ./nfield decomposition 7 --lag 1
```

**Then watch the $L$-values appear.** Run the correlation at base $5$ first. It will be exactly $1.00$. Both factors encode the same $L$-value, so the collision coefficient squares it. Now try base $13$. Then $31$. Then $71$. The correlation drops, slowly, but it stays above $0.83$ even with $2{,}450$ characters. The singer is still audible over the crowd. You are watching the digit function encode the $L$-function landscape, and the encoding does not break.

```
$ ./nfield sg_correlation --bmax 71
```

**Finally, see the weighted majorant.** The decomposition theorem reveals that the primitive odd sector of the transform sits beneath an explicit weighted sum of $L$-function data. Run it at a prime base. The number on screen is finite. That finite number comes from counting digit collisions, but after factorization it lives in the same expression as Bernoulli numbers, diagonal sums, and prime character data.

```
$ ./nfield moment_bound 11 --lag 1
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Collision Spectrum and the L-Function Landscape](https://github.com/alexspetty/nfield/blob/main/research/collision_spectrum_landscape.pdf)
Preprint: [The Collision Spectrum](https://arxiv.org/abs/2604.00054)

---

*Alexander S. Petty*
March 2025 (updated April 2026)
.:.
