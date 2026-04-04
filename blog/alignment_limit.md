# The Alignment Limit for All Primes

The digit-partitioning primes are the easy ones. Three of them in base 10. Clean separation, clean formula, clean limit. But the infinite world beyond them, every prime from 13 onward, has collisions. Remainders forced to share bins. The old formula breaks, and finding the new one required looking more carefully at what the digit function actually builds.

Beyond the digit-partitioning boundary, collisions are inevitable. The digit function sorts $p - 1$ remainders into $b$ bins, and when $p > b + 1$, some bins hold more than one. The sum of squared bin sizes

$$S(p,b) = \sum_{d=0}^{b-1} n_d^2$$

measures the total collision. For digit-partitioning primes, $S = p - 1$ (one per bin). For $p = 17$ in base 10, $S = 28$. For $p = 101$, $S = 1000$. The collisions grow, and they have structure. The question is not whether they happen. It is how they organize.

## The coset

Here is where something unexpected happened.

When you do long division, the remainders cycle. At $p = 7$ in base 10, the cycle visits every remainder: 1, 3, 2, 6, 4, 5, and back to 1. A complete tour. But at larger primes, the cycle often does not visit every remainder. It visits a subset. A specific subset, determined by the base, called an orbit.

I had assumed the orbit was always the same. For a given prime $p$, the base $b$ generates a cycle, and every denominator built from $p$ would trace the same cycle. The same remainders visited in the same order.

It isn't the same. The orbit depends on $m$.

When you compute $1/(pm)$ in base $b$, the smooth factor $m$ shifts the starting point. The cycle that the repetend traces is not the orbit of $b$ itself. It is a parallel orbit, offset by a quantity that depends on $m$. Mathematicians call this a *coset*: a copy of the original orbit, shifted to start somewhere else. The cosets tile the group without overlapping, like parallel lanes on a track. Change $m$ and you change which lane you are in. Different lane, different remainders visited, different bins, different alignment.

The alignment is not just a function of $p$. It is a function of $p$ and which track $m$ puts you on. I had been assuming one variable and there were two.

## The exact formula

Once the coset is visible, the formula follows. As far as I can tell, this result is new. For any prime $p$, any base $b$, and any smooth $m$:

$$\alpha(pm) = \frac{m - 1 + m \cdot T(C_m) / L}{pm - 1}$$

where $L$ is the multiplicative order of $b$ modulo $p$, and $T(C_m) = \sum_{r \in C_m} n_{\delta(r)}$ sums the bin sizes visited by the coset $C_m$.

This is exact at every finite $m$. No limit, no approximation, no conjecture. The coset bin sum $T$ determines the alignment completely. The formula for digit-partitioning primes, $(2m-1)/(pm-1)$, is the special case where every bin has size 1 and $T = L$. I found the formula computationally, by tracking alignment values across thousands of denominators and noticing that the oscillations organized by coset. The proof came after.

## One prime, many limits

When $b$ is a primitive root modulo $p$, the orbit visits every residue. One coset. One bin sum. One limit. The alignment converges to a single value as $m$ grows, and the formula gives it exactly.

When $b$ is not a primitive root, the residues split into multiple cosets. The orbit visits only one of them, and which one depends on $m$. Different smooth values of $m$ land in different cosets. Different cosets visit different bins. The alignment does not converge. It oscillates.

At $p = 53$ in base 10, the multiplicative order is 13. Four cosets. Two of them produce alignment approaching $80/689$. The other two approach $82/689$. The alignment limit, as a single number, does not exist. The sequence of smooth $m$ values wanders between cosets, and the alignment wanders with it.

I had expected a formula with one answer per prime. The mathematics gave me a formula with one answer per coset. The structure of $(\mathbb{Z}/p\mathbb{Z})^{*}$ enters through the back door, and it refuses to average away.

## The golden bound

Despite the branching, one result holds unconditionally. For any coset, any $m$, and any prime $p \ge 5$:

$$\alpha(pm) < \frac{1}{\varphi}$$

Each coset element contributes at most $\lceil(p-1)/b\rceil$ to the bin sum. This gives

$$\alpha \le \frac{p+1}{2p}$$

which falls below $1/\varphi$ for all $p \ge 5$.

The golden ratio's selection of the prime 3, proved for digit-partitioning primes in [an earlier note](https://github.com/alexspetty/nfield/blob/main/research/golden_ratio_selects_prime_three.pdf), extends to all primes unconditionally. No matter which coset you land in, no matter how large $m$ grows, no prime beyond 3 reaches the golden threshold. The coset structure complicates the exact value of the alignment. It does not touch the bound.

The remainders fall like light through a prism, separating into bins. Each bin catches a different color, a different weight. In the digit-partitioning world, every bin held exactly one ray and the spectrum was perfectly resolved. Here, some bins catch two rays, three, ten. The colors overlap. The weight accumulates unevenly. What was partition has become accumulation. And the golden threshold still floats above it all, untouched.

The quantity $S = \sum n_d^2$ that governs all of this is the starting point for the [collision invariant](https://arxiv.org/abs/2604.00045), which connects the digit function to Dirichlet characters and L-function special values.

## Try it yourself

Look at the collisions at $p = 23$. The bins are more crowded:

```
$ ./nfield field 23
```

Now watch what happens at $p = 53$ as the smooth factor $m$ grows. The alignment should converge to a single limit. It doesn't:

```
$ ./nfield align 53       # 0.0991
$ ./nfield align 106      # 0.1106  (m=2)
$ ./nfield align 212      # 0.1119  (m=4)
$ ./nfield align 265      # 0.1157  (m=5, different coset)
$ ./nfield align 530      # 0.1144  (m=10, back again)
```

The values wander. They do not settle. Each smooth $m$ lands in a coset, and the coset determines the alignment. Four cosets at $p = 53$, four possible limits, and the sequence of smooth $m$ visits them in no fixed order.

Now compare with $p = 3$, where the alignment does converge:

```
$ ./nfield align 3        # 1.000
$ ./nfield align 6        # 0.600
$ ./nfield align 12       # 0.636
$ ./nfield align 24       # 0.652
$ ./nfield align 96       # 0.663
```

Steady climb toward $2/3 \approx 0.667$. One coset. One limit. Above $1/\varphi \approx 0.618$.

The prime 53 wanders between 0.099 and 0.116. The prime 3 climbs to 0.667. The golden threshold separates them, and nothing in the coset structure changes that.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Alignment Limit for All Primes](https://github.com/alexspetty/nfield/blob/main/research/alignment_limit.pdf)

---

*Alexander S. Petty*
August 2021 (updated March 2026)
.:.
