# The Neutrality Theorem

[The collision transform and the critical strip](https://alexpetty.com/the-collision-transform-and-the-critical-strip/) ended with a discovery I could not let go. The centered collision sum converges at $s = 1$. That is a theorem. It also appears to converge below $s = 1$, reaching into the critical strip where the zeros of $L$-functions live. That is an observation. And when I removed the mod-$3$ structure from the collision coefficients, the penetration died. The sum still converged at $s = 1$, but below it the numbers ran away. The mod-$3$ structure was holding the sum together, and I had no idea why.

This paper is my attempt to find out.

## Two pieces, both divergent

Every prime larger than $3$ leaves a remainder of $1$ or $2$ when you divide it by $3$. That is just a fact about primes. They cannot be divisible by $3$, so they land on one side or the other. What I found is that the collision deviation cares which side. Primes that are $1 \pmod 3$ carry a slightly different average deviation than primes that are $2 \pmod 3$. The difference is small, but it never goes away. It is baked into the structure.

In [the centered collision sum](https://alexpetty.com/the-centered-collision-sum/) I removed the per-family bias (the bias that depends on the prime's last digit) and the sum converged at $s = 1$. Now I am looking at a second bias hiding underneath, one that depends not on the last digit but on the remainder mod $3$. Two layers of bias, nested inside each other.

So I split the centered sum into two pieces. One piece, $\mathcal{M}$, captures the mod-$3$ bias alone. The other piece, $F^{\circ\circ}$, is what remains after both biases are removed, the *doubly centered* deviation, stripped of everything predictable. The centered sum splits cleanly:

$$F^\circ(s) = F^{\circ\circ}(s) + \mathcal{M}(s)$$

I computed both pieces separately. Here is what I saw.

```
  s       F°        F°°         M       1 + F°°/M
-----   ------   ---------   --------   ---------
 1.0     +0.08       +0.90     -0.82       -0.10
 0.9     +0.12       +2.38     -2.26       -0.05
 0.8     +0.18       +7.25     -7.07       -0.03
 0.7     +0.27      +25.2     -24.9        -0.011
 0.6     +0.37      +96.6     -96.2        -0.004
 0.5     +0.37     +399.6    -399.2        -0.001
```

Look at the middle two columns. At $s = 0.5$, the doubly centered sum has grown to $+400$. The mod-$3$ component has grown to $-400$. Both are diverging, hard, in opposite directions.

Now look at the first data column. $F^\circ$ sits at $0.37$ and does not move.

The two divergences are destroying each other. The last column measures how far their ratio is from $-1$. If the cancellation were perfect, that column would read $0$. At $s = 0.5$ it reads $-0.001$. The ratio between the two divergent pieces is $-0.999$, missing perfect cancellation by one part in a thousand, and the gap shrinks as the prime count grows. Two sums, each blowing up, perfectly matched, leaving behind a finite residue that barely twitches.

I had seen cancellation before in this program. The per-family centering at $s = 1$ is a cancellation. But that one operates by subtraction. You remove a known bias and the remainder converges. This is different. Neither piece converges on its own. The convergence exists only in the combination. Take either piece away and you have infinity. Put them together and you have $0.37$.

## How perfect is perfect

The natural question. Is the cancellation exact, or is it leaking? If the two divergences are not quite matched, the residue will eventually grow, and the convergence is an illusion that breaks at larger ranges.

I fitted the data to the form

$$\vert 1 + F^{\circ\circ} / \mathcal{M} \vert \sim C / \vert F^{\circ\circ} \vert^{\alpha}$$

where $\alpha$ measures the quality. At $\alpha = 1$ the residual shrinks as fast as the divergence grows. Perfect cancellation, bounded sum. At $\alpha < 1$ the cancellation is losing ground.

```
primes          s       F°        F°°       1+ratio     alpha (fit)
----------    -----   ------   ---------   ---------   -----------
   10,000      0.7     +0.27      +7.1       -0.039        0.58
  100,000      0.7     +0.28     +13.1       -0.022        0.61
  348,488      0.7     +0.29     +18.1       -0.016        0.62
  700,000      0.7     +0.26     +21.6       -0.012        0.91
1,270,000      0.7     +0.27     +25.2       -0.011        0.75
```

At $348{,}488$ primes the fit gives $\alpha \approx 0.6$. Not $1$. But the exponent drifts upward as the range grows. The fit is noisy, because at finite range the character sum corrections are still competing with the Mertens divergence. As the Mertens term grows and dominates, the corrections shrink to nothing and $\alpha$ should approach $1$.

Should. But I did not want to trust a numerical trend. I wanted to know if the cancellation is exact by structure, not by accident.

## The algebra settles it

It is exact by structure. Here is why, and I want to walk through this carefully because the argument is short and the conclusion is permanent.

The mod-$3$ component $\mathcal{M}$ depends only on one thing about each prime, whether it is $1$ or $2$ mod $3$. That is a binary choice. And whenever you have a function that makes a binary choice across two classes, you can split it into two pieces. One piece treats every prime the same, assigning the value $1$ to all of them regardless of class. That is the *trivial character*. The other piece distinguishes the classes, assigning $+1$ to primes that are $1 \pmod 3$ and $-1$ to primes that are $2 \pmod 3$. That is the *non-trivial character* $\chi_3$. Between these two pieces, you can reconstruct any function that depends only on the mod-$3$ class.

The mod-$3$ component splits into exactly these two pieces:

$$\mathcal{M}(s) = c_0 \sum_p \frac{1}{p^s} + c_1 \sum_p \frac{\chi_3(p)}{p^s}$$

Now look at what each piece does. The first sum adds up $1/p^s$ over every prime, weighting them all equally. That is the prime harmonic series, and it diverges. It grows like $\log \log x$, the same Mertens drift from [the collision fluctuation sum](https://alexpetty.com/the-collision-fluctuation-sum/). The second sum flips sign depending on the prime's class, adding $+1/p^s$ for one and $-1/p^s$ for the other. The positives and negatives wash each other out, and the sum converges. Dirichlet proved this in the 1830s. So the entire divergence of $\mathcal{M}$ lives in the first piece, the trivial character, the one that treats every prime the same.

Here is where it clicks.

The full centered sum $F^\circ$ also has a character decomposition, via the collision transform. But the antisymmetry theorem from [the centered collision sum](https://alexpetty.com/the-centered-collision-sum/) kills every even character, and the trivial character is even. It is gone. $F^\circ$ contains no trivial character at all. No $\sum 1/p^s$. No Mertens term. No divergence.

That is the whole proof. The mod-$3$ component $\mathcal{M}$ carries a Mertens divergence. The doubly centered sum $F^{\circ\circ}$ carries the same divergence with opposite sign. In their sum $F^\circ$, the two cancel exactly, because $F^\circ$ was never allowed to have a Mertens term in the first place. The antisymmetry killed it at birth.

The cancellation exponent is $\alpha = 1$. Not approximately. Not trending toward it. Exactly $1$, by algebra, whenever the mod-$3$ bias is present ($c_0 \neq 0$). When $3$ divides the base, $c_0 = 0$ and there is no cancellation to measure, the doubly centered sum *is* the centered sum. The data was telling the truth all along.

## The class that does nothing

The algebra proves the cancellation is perfect. But it does not explain *why*. Why does the collision invariant have a mod-$3$ structure in the first place? What is special about $3$?

The answer comes from the reflection identity, and it is simple enough to see without any formulas.

Every number $a$ has a complement $m - a$. The collision invariant pairs them and forces their values to add up to $-1$. Always. At every prime, in every base. If one partner has a collision deviation of $+2$, the other has $-3$. If one has $0$, the other has $-1$. The pair always sums to $-1$, so the pair always averages to $-1/2$.

Now divide all the units into three groups based on their remainder mod $3$. Group $0$, group $1$, group $2$. The reflection, the map that sends $a$ to $m - a$, shuffles these groups. Which group maps to which depends on $m \bmod 3$. At lag $1$, the modulus is $m = b^2$, and since $b$ is not divisible by $3$, we get $b^2 \equiv 1 \pmod 3$. That means the reflection sends group $0$ to group $1$ and group $1$ back to group $0$. Those two groups swap partners across the divide.

But group $2$ maps to itself.

Every unit in group $2$ is paired with another unit in group $2$. The reflection does not send them anywhere else. And since every pair averages to $-1/2$, the average of the entire group is exactly $-1/2$, which is exactly the overall average across all groups.

Group $2$ is neutral. It sits at the center of mass and contributes nothing to the mod-$3$ bias. It does not pull the sum in either direction. It is dead weight, perfectly balanced, invisible to the cancellation mechanism.

All the action is in groups $0$ and $1$, which the reflection swaps. Their averages are forced to be equal and opposite. One pulls up, the other pulls down, by the same amount. Since primes above $3$ can only be $1$ or $2$ mod $3$ (never $0$, because that would make them divisible by $3$), the prime sum sees one group that pulls (group $1$) and one that does not (group $2$). The entire cancellation is a group-$1$ phenomenon.

That is the neutrality theorem at lag $1$. I have verified it at every base up to $40$ where $3$ does not divide $b$. It is not approximate. The identity $2 \cdot \text{sum}_2 = -\text{count}_2$ holds exactly, as an integer equation, at every base I have tested. The reflection forces it.

At higher lags the picture is slightly more general. The neutral class is whichever group the reflection fixes, and that depends on $m \bmod 3$. When $m \equiv 1 \pmod 3$ (which includes every lag-$1$ case), group $2$ is neutral. When $m \equiv 2 \pmod 3$, group $1$ is neutral instead. The theorem is the same either way: one group is fixed by reflection, that group is neutral, and the other two swap. The research note works out the general case.

## The three regimes

The strength of the mod-$3$ bias varies across bases:

```
base    phi(b^2)     c_0        F°(0.5)     |F°°(0.5)|    type
----    --------    ------     ---------    -----------   ------
  3         6       0            +0.65          0.65      3 | b
  5        20      +0.11         +0.88           51       weak
  7        42      -0.70         +1.76          323       strong
 10        40      -0.65         +0.09          296       strong
 11       110      +0.02         +1.72          8.3       weak
 12        48       0            -0.64          0.64      3 | b
 13       156      -0.80         +3.53          369       strong
```

Three regimes. When $3$ divides the base (bases $3$, $6$, $9$, $12$), the mod-$3$ bias vanishes entirely. There is no class $0$ among the units, the splitting does not arise, and $F^\circ = F^{\circ\circ}$. The doubly centered sum *is* the centered sum, no cancellation needed.

When $3$ does not divide the base and $|c_0|$ is large (bases $7$, $10$, $13$), the Mertens term dominates early. The fitted $\alpha$ approaches $1$ quickly. These are the strong-bias bases, and the convergence is visible at modest prime counts.

When $3$ does not divide the base but $|c_0|$ is small (bases $5$, $11$), the character corrections remain comparable to the Mertens term for a long time. The finite-range $\alpha$ stays low. Not because the cancellation is imperfect, but because the asymptotic regime has not arrived yet. Give it more primes and $\alpha$ will climb. The theorem says it reaches $1$ whenever $c_0 \neq 0$.

## The constant from paper one

I want to close with something that stopped me cold when I first computed it.

In [the golden ratio selects prime three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/), the very first paper in this sequence, the alignment limit at the prime $3$ came out to $2/3$. That constant fell out of a self-referential cubic through the golden ratio. It was the number that started the whole program.

Seventeen papers later, I computed the mod-$3$ class means in base $3$ at lag $1$.

```
class 1 mean:   -2/3
class 2 mean:   -1/3
```

The splitting ratio between the two classes is $2/3$. The alignment limit. The same constant, arrived at through a completely different computation, sitting inside a completely different structure.

I did not put it there. The digit function computed it, and the golden ratio's constant was waiting inside the answer. The collision program is not a line. It is a web, and the threads run backward as often as they run forward.

## A note from 2026

*April 2026*

The neutrality theorem became the structural anchor for the conditional penetration result in [The Collision Transform](https://arxiv.org/abs/2604.00047) preprint. The perfect cancellation ($\alpha = 1$) is the reason the centered sum contains no Mertens term, and that absence is what allows the sum to converge below $s = 1$ wherever the $L$-functions have no zeros. The neutrality of the fixed reflected class is the mechanism, and the reflection identity is its proof.

The three-regime classification (divisible by $3$, strong bias, weak bias) also survived into the preprint. It explains the base-dependent convergence rates from [the critical strip paper](https://alexpetty.com/the-collision-transform-and-the-critical-strip/). Strong-bias bases show fast convergence of $\alpha$ toward $1$, while weak-bias bases need more primes before the Mertens term dominates.

The next paper, [the general neutrality theorem](https://alexpetty.com/the-general-neutrality-theorem/), extends the result from mod $3$ to arbitrary small primes $q \nmid b$. The structure at mod $3$ turns out to be the simplest case of a general pattern, and the reflection identity that proves neutrality at $q = 3$ proves it at every $q$.

.:.

---

## Try it yourself

Split the centered sum into its two pieces and watch them diverge in opposite directions. The doubly centered column and the mod-$3$ column will grow toward $\pm 400$ at $s = 0.5$. The centered sum column will sit near $0.37$ and refuse to move. That is the cancellation, live.

```
$ ./nfield neutrality 10 --lag 1
```

Now check the neutrality theorem directly. Print the mod-$3$ class means and verify that group $2$ lands at exactly $-1/2$. Then add the means of groups $0$ and $1$. They should sum to exactly $-1$. Not approximately. Exactly. The reflection forces it.

```
$ ./nfield mod3_means 10 --lag 1
```

Try the same thing in base $3$. The class means should come out to $-2/3$ and $-1/3$. That splitting ratio is $2/3$, the alignment limit from [the golden ratio selects prime three](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/). Then try base $7$, base $13$, base $11$. Watch the three regimes appear. Strong bias, weak bias, and no bias at all when $3$ divides the base.

```
$ ./nfield neutrality_sweep --lag 1
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Neutrality Theorem](https://github.com/alexspetty/nfield/blob/main/research/neutrality_theorem.pdf)

---

*Alexander S. Petty*
April 2024 (updated April 2026)
.:.
