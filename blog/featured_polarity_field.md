# Convergence of Collision Fluctuation Sums

**Preprint**

In 2009 I drew a circle with nine positions and placed the integers on it. I colored the residue classes and watched where the primes landed. I saw something I could not explain: the complement classes avoided each other. I called it polarity. You can see the original drawings in my [earlier notes on numeric polarity](https://alexpetty.com/on-numeric-polarity-and-the-distribution-of-primes/).

I knew what I was seeing. I did not yet have the language to say it precisely. This paper provides the language.

## The polarity field

The centered collision invariant $F(a) = S^\circ(a)$ is a function on the coprime classes modulo $b^2$. It satisfies $F(a) + F(b^2 - a) = 0$: antisymmetric under the complement map. It decomposes entirely into odd Dirichlet characters. It cancels across primes (the collision PNT) but persists in amplitude (the variance theorem).

This is the polarity field. It is a signed, antisymmetric, constant-amplitude vibration on the finite group, defined by the digit function, encoding L-values through the decomposition theorem.

## The three involutions

The paper identifies three involutions that correspond across levels of structure:

The complement map $a \mapsto b^2 - a$ on the group. This creates the polarity field by forcing the collision invariant into odd characters. Level 1.

The conjugation $\chi \mapsto \overline{\chi}$ on the character group. This separates even from odd. The polarity field lives entirely in the odd characters because the complement map forces it there. Level 2.

The functional equation $s \mapsto 1 - s$ for L-functions. Its fixed line is $\operatorname{Re}(s) = 1/2$, the critical line, where the Riemann Hypothesis places the zeros. Level 3.

<div>
$$a \mapsto b^2 - a \quad\longleftrightarrow\quad \chi \mapsto \overline{\chi} \quad\longleftrightarrow\quad s \mapsto 1 - s$$
</div>

One involution at three levels. The complement map on the circle. The conjugation on characters. The functional equation on the strip. The polarity field connects them.

## The avoidance

The collision weights $|\hat{c}(\chi)|^2$ and the prime character sums $|P(s, \chi)|^2$ weight the same set of characters. The avoidance deficit measures their interaction:

<div>
$$D(s) = 1 - \frac{\sum |\hat{c}|^2 |P(s)|^2}{(\sum |\hat{c}|^2)(\text{mean}\, |P(s)|^2)}$$
</div>

When $D > 0$: the collision-weighted mean of $|P|^2$ is smaller than the unweighted mean. Characters that the collision invariant favors carry small prime sums.

In base 10, with 664,579 primes:

| $s$ | $D(s)$ | Pearson $r$ | |
|-----|---------|-------------|---|
| 2.00 | $-0.14$ | $+0.36$ | correlated |
| 1.20 | $+0.09$ | $-0.33$ | avoidance begins |
| 1.00 | $+0.19$ | $-0.58$ | strong avoidance |
| 0.50 | $+0.55$ | $-0.71$ | maximal avoidance |

Above the critical strip: correlation. Inside the strip: anti-correlation. The avoidance begins near $s = 1.3$ and grows monotonically toward $s = 1/2$. The rank reversal is complete: the pair of characters with the largest collision weight carries the smallest prime sum, all the way down.

Across bases:

| Base | $D(1)$ |
|------|--------|
| 5 | $+0.57$ |
| 7 | $+0.48$ |
| 10 | $+0.19$ |
| 11 | $+0.52$ |
| 13 | $+0.48$ |

Every base shows avoidance. The effect is universal.

## The convergence equivalence

The paper proves: $F^\circ(\sigma)$ converges for $\operatorname{Re}(s) > 1/2$ if and only if GRH holds for all L-functions in the decomposition. The polarity field's convergence is equivalent to the zeros being on the critical line.

This is a bi-conditional. If the polarity field converges in the strip, GRH holds for these characters. If GRH holds, the polarity field converges. The collision invariant and the Riemann Hypothesis are two views of the same condition.

## The $\mathbb{Q}(\sqrt{5})$ reduction

In base 10, the squared diagonal sums decompose over $\mathbb{Q}(\sqrt{5})$: each $|S_G(\chi)|^2$ has the form $A_k + 2\epsilon_k\sqrt{5}$ for explicit integers $A_k$ and signs $\epsilon_k$. The avoidance deficit $D(\sigma) > 0$ reduces to a single inequality involving the $\sqrt{5}$ components of the prime character sums.

The golden ratio's number field, which selected the prime 3 in the program's first result, reappears here at the deepest level. The avoidance between collision weights and prime sums is controlled by the $\sqrt{5}$ part of the character data. The rational part cancels. The irrational part decides.

## What this means

An arithmetic object defined by the digit function avoids the L-function peaks in the critical strip. The avoidance is maximal where the zeros live.

The mechanism is the three-link chain proved in the companion paper on zero density: large collision weight implies large $|L(1)|$ (decomposition theorem), which implies zeros far from $s = 1$ (Hadamard product), which implies small prime sums (explicit formula). The digit function's geometry selects for L-functions with well-organized zeros.

The avoidance grows toward $\operatorname{Re}(s) = 1/2$, the fixed line of the functional equation, the line where the three involutions align. The complement map created the polarity field. The functional equation constrains the zeros. The avoidance is the relationship between them: what the digit function measures and where the zeros live are on opposite sides of the character spectrum.

A circle on the left, divided into paired arcs, each glowing with signed intensity. Positive on one side, negative on the complement. The pairs balance exactly. Beside the circle, a vertical strip, narrow and luminous, with a faint line at its center. The arcs that glow brightest on the circle correspond to the quietest channels in the strip. The arcs that are faint on the circle carry the loudest signals in the strip. The two forms face each other across the dark space between them: the group and the complex plane, connected by the same involution, seeing the same structure from two distances.

I first drew the circle in 2009. I saw the polarity. I did not know it had a name, or that it factored through Bernoulli numbers and L-values, or that it would avoid the prime peaks in the critical strip. The mathematics was already there, in the pairing of the residue classes, in the antisymmetry of the complement map. It took time to learn how to read it.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)

*Alexander S. Petty*
April 2026
.:.

