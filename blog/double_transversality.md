# The Double Transversality

The collision invariant and the prime distribution were avoiding each other. [The General Neutrality Theorem](https://alexpetty.com/the-general-neutrality-theorem/) showed it: the channels where the collision invariant puts its biggest weights are the channels where the primes respond the least. The two signals dodge each other across the frequency spectrum.

That avoidance, the anti-correlation, was measured at lag $1$ in a handful of bases. Two questions followed me out of that paper.

Does the avoidance survive when the number of channels grows from a handful to thousands?

And what happens if you stop looking at one base at a time and add the signals from different bases together?

## Into deeper water

The lag is how far apart two copies of the digit function are shifted before you compare them. At lag $1$, you compare adjacent digits. At lag $2$, you skip one. At lag $7$, you skip six. Higher lags see finer structure, but the price is that the number of frequency channels grows exponentially. At base $3$, lag $1$, there are $3$ channels. At lag $7$, there are $2{,}187$. If the avoidance were a coincidence of small numbers, it would dissolve as the channel count grew, the way a pattern in a small sample disappears when you collect more data.

I ran the computation at every lag.

```
base    lag    modulus    channels    net F°(0.5)    correlation
----    ---    -------    --------    -----------    -----------
  3      1          9          3         +0.62          +0.00
  3      2         27          9         +1.18          +0.42
  3      3         81         27         +0.62          -0.42
  3      4        243         81         +4.83          -0.28
  3      5        729        243        +12.8           -0.33
  3      6      2,187        729        +29.1           -0.33
  3      7      6,561      2,187        +11.1           -0.20
  5      1         25         10         +1.04          -0.45
  5      2        125         50         +4.01          -0.18
  5      3        625        250         +2.48          -0.28
  5      4      3,125      1,250        +15.3           -0.19
  7      1         49         21         +1.81          -0.28
  7      2        343        147         +7.56          -0.22
  7      3      2,401      1,029         +4.58          -0.16
```

The last column is the correlation between how heavy a channel's collision weight is and how large that channel's prime sum is. Negative means they are avoiding each other. Zero or positive means they are not.

At the smallest cases (base $3$, lags $1$ and $2$, where there are only $3$ or $9$ channels), the correlation has not settled. There are too few channels to measure a meaningful trend. But from lag $3$ onward, every row is negative. From $27$ channels to $2{,}187$ channels, the avoidance persists. The collision invariant keeps putting its weight on the quiet channels and leaving the loud ones alone.

It did not dissolve in the tested range.

![Anti-correlation persists across lags](https://alexpetty.com/content/images/2026/04/post20_lag_persistence-1.png)

And look at the net column. The net is positive at every row, and it is growing. At base $3$, it climbs from $+0.62$ at lag $1$ to $+29.1$ at lag $6$. Whatever the digit function is doing, the computation sees more of it as the scale grows, not less.

## The disappearing signal

Now the second question, and this is the one that rearranged my thinking.

Each base has its own collision invariant, its own channel decomposition, its own pattern of avoidance. I had been studying them one at a time, the way you might study individual instruments in an orchestra. I had never asked what happens when you play them all at once.

I computed the net collision signal at ten prime bases individually.

```
base    F°(0.5)
----    -------
  3      -0.03
  5      -0.00
  7      +0.07
 11      -1.36
 13      -0.18
 17      -0.09
 19      -0.55
 23      -1.30
 29      +2.80
 31      +5.07
```

Each base produces a real number. Some are positive, some negative. The range spans $6.4$ units. Each collision invariant is doing something real.

![Base-specific signals cancelling](https://alexpetty.com/content/images/2026/04/post20_base_signals.png)

Then I took the weighted sum across all ten bases.

```
  s       base sum    min F°     max F°     range
-----    ---------    ------     ------     -----
  1.0      -0.000     -0.04      +0.21      0.25
  0.8      -0.001     -0.15      +0.78      0.93
  0.6      -0.006     -0.66      +2.80      3.46
  0.5      -0.010     -1.36      +5.07      6.43
```

The base sum is $-0.01$.

A range of $6.4$, compressed to $-0.01$. Ten bases, each carrying a signal, and in this finite experiment the signals destroy each other almost perfectly.

Each collision invariant avoids the prime-sensitive channels, but they avoid them in *different directions*. Base $31$ dodges left. Base $11$ dodges right. Base $3$ barely dodges at all. Each one finds its own way around the obstacle, and when you average all the dodges together, they cancel. The structural content of the collision invariant appears to be base-specific. It does not survive aggregation.

## Two kinds of avoidance

This is what I call the double transversality. It is an observed pattern, not a proved theorem. But the pattern has two clear layers.

**First layer: within each base, the collision invariant avoids the prime-sensitive channels.** The channels that respond most strongly to the primes (and therefore to $L$-function zeros) are the channels where the collision invariant puts its smallest weights. This is the anti-correlation from [the general neutrality theorem](https://alexpetty.com/the-general-neutrality-theorem/). It is the leading candidate mechanism behind the observed convergence at each base.

**Second layer: across bases, the avoidance directions cancel.** Each base dodges the prime-sensitive channels in its own direction. When you add up the dodges, they point in enough different directions that the sum is nearly zero.

Each base appears to provide partial information about a related underlying structure, but the bases emphasize different components. Combining them averages out the base-specific contributions, leaving little net signal.

The collision invariant is not behaving like a universal measurement in these experiments. It is acting like a base-specific view of something universal. The signal is real at each base, but it seems to be real for base-specific reasons, and those reasons do not add up to a single global explanation.

One subtlety. The vanishing of the base sum does not mean combining bases is useless. [The neutrality theorem](https://alexpetty.com/the-neutrality-theorem/) operates at the level of individual primes, not sums over primes. The individual-prime structure survives aggregation. The sum-over-primes structure does not. The double transversality is about the sum, not the primes.

This is not a defect. In these computations, it suggests what the collision invariant is doing. The digit function's geometry, projected onto the frequency channels at an angle that avoids the primes. Change the base, and the angle rotates. The avoidance persists. The direction does not.
## A note from 2026

*April 2026*

The double transversality was a turning point in how I understood the program. Before this paper, I thought the collision invariant might be detecting a universal property of $L$-function zeros, something that would survive base-aggregation and point toward a single deep truth. The near-vanishing base sum in the tested family killed that idea for me. The collision invariant's relationship to zeros looks base-specific and non-aggregable.

That turned out to be the right framing for the later papers. [The collision spectrum](https://alexpetty.com/the-collision-spectrum-and-the-l-function-landscape/) decomposes the invariant into Bernoulli numbers and diagonal character sums, and both of those quantities are base-dependent. The polarity field measures the avoidance directly, and it varies with the base. The base-specificity is not an obstacle. It is the structure.

The higher-lag persistence also mattered. The anti-correlation holding in the tested range from $3$ channels to $2{,}187$ channels means it is not behaving like a small-number artifact. Whatever the digit function is doing, the computation sees it at every tested scale. That observation fed directly into the zero-density theorem, which studies how the collision weights select for characters whose $L$-functions have no nearby zeros.

.:.

---

## Try it yourself

Run the anti-correlation at higher lags. The last column should stay negative as the number of channels climbs from tens to thousands. If the avoidance were a small-number artifact, you would expect it to fade. It does not fade.

```
$ ./nfield anticorrelation 3 --lag 1 --lagmax 7
```

Compute the collision signal at each prime base individually. Some will be positive, some negative, and the spread will be wide. Each base is seeing something real.

```
$ ./nfield base_sweep --lag 1 --bmax 31
```

Now take the weighted sum. The range was $6.4$. The sum should land near zero. Ten real signals, nearly destroying each other.

```
$ ./nfield base_sum --lag 1 --bmax 31
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Double Transversality](https://github.com/alexspetty/nfield/blob/main/research/double_transversality.pdf)

---

*Alexander S. Petty*
October 2024 (updated April 2026)
.:.
