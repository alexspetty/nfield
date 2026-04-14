# The General Neutrality Theorem

[The neutrality theorem](https://alexpetty.com/the-neutrality-theorem/) proved that the prime $3$ controls the cancellation below $s = 1$. The reflection fixes one residue class mod $3$, that class is neutral, and the Mertens divergence cancels algebraically.

The natural question was whether $3$ is special. I generalized the argument to every odd prime in an afternoon. The proof is identical. Replace $3$ with any odd prime $q$, check that $2$ is invertible mod $q$ (it always is, because $q$ is odd), and the fixed class exists and is unique. One neutral class, $(q-1)/2$ swapped pairs, means summing to $-1$. The same theorem, at every prime scale, from the same reflection identity.

That generalization was easy. What I found *inside* the generalization was not.

## The same lock, every door

Take any odd prime $q$ not dividing the base. The reflection sends residue class $k$ to class $m - k \pmod q$. The equation $2k \equiv m \pmod q$ has exactly one solution. That class is fixed. The reflection pairs its units with each other, each pair averages to $-1/2$, and the class mean lands at exactly the grand mean. Not near it. On it.

At $q = 3$, one neutral class, one swapped pair. At $q = 5$, one neutral class, two swapped pairs. At $q = 7$, one neutral class, three pairs. The partition gets finer with each prime, but the neutral class is always there, always at the center.

```
base    q     neutral class    2·sum + count
----    --    -------------    -------------
  5      3          2                0
  5      7          2                0
  7      3          2                0
  7      5          2                0
 10      3          2                0
 10      7          1                0
 13      3          2                0
 13      5          2                0
 13      7          1                0
```

I tested every combination of base up to $20$ and prime up to $19$ where the prime does not divide the base. That gives $117$ cases. Every row reads zero. The proof at $q = 97$ is the same proof as at $q = 3$. The reflection identity does not care which prime you use. It constrains them all.

And the constraints hold simultaneously on the combined CRT period. For any finite set of odd primes $q \le Q$ not dividing the base, you can lift the collision invariant to the period that sees all of those congruence conditions at once. On that lifted period, the fraction of points that avoid neutrality at every one of those primes is exactly

$$\prod_{q \le Q}\frac{q-1}{q}$$

and Mertens' theorem drives that product to zero. As you include more primes, fewer lifted points escape. The collision invariant is not just constrained at one scale. It is constrained at every scale, simultaneously, and the constraints compound until nothing escapes.

A random function on the units would satisfy none of this. The collision invariant satisfies all of it.

But here is the thing. The generalization told me the collision invariant is pinned at every prime. It did not tell me what those pins *do* to the convergence. For that, I had to look at the character decomposition more carefully. And what I found there made me rethink the entire program.

## The assumption I never checked

The centered sum $F^\circ$ decomposes over odd Dirichlet characters. Each character $\chi$ contributes a product. On one side, the collision coefficient $\hat{S}^\circ(\chi)$, the weight the collision invariant assigns to that character. On the other, the prime character sum $P(s, \chi)$, the way that character reads the distribution of primes. Multiply them together and you get one term in the sum. Add up all the terms and you get $F^\circ(s)$.

For months I had been carrying an assumption without realizing it. I assumed all these products pointed in the same direction. If they did, convergence of $F^\circ$ at $s = 1/2$ would force each $P(s, \chi)$ to converge individually, and that would be equivalent to GRH for the odd $L$-functions modulo $m$. The collision transform would be a machine that tests the Riemann Hypothesis character by character.

I finally checked.

They do not all point in the same direction.

```
  s      positive    negative    sum(+)    sum(-)     net
-----    --------    --------    ------    ------    -----
  1.0       13           7       +0.47     -0.39     +0.08
  0.8       15           5       +0.28     -0.10     +0.19
  0.6       13           7       +0.75     -0.31     +0.44
  0.5       13           7       +1.46     -0.73     +0.73
```

Seven of twenty products are negative at $s = 0.5$ in base $10$. The net is positive not because the positives outnumber the negatives, but because they outweigh them in magnitude. Thirteen terms pull the sum toward convergence. Seven pull against it. The thirteen win, but only by being larger, not by being more numerous.

I sat with this table for a long time. It meant the collision transform is not a GRH detector. Mixed signs mean the convergence of $F^\circ$ does not require each character sum to converge on its own. An $L$-function could have a zero with real part above $1/2$, and the collision weighting could absorb the resulting divergence through a term of opposite sign. The sum could converge even if individual $L$-functions misbehave, as long as the misbehavior gets cancelled by the collective weighting.

This was not what I expected. It was better.

## The instrument that looks past the zeros

If the signs are mixed, why does the net come out positive? Why do the thirteen winning terms consistently outweigh the seven losing ones? What is special about the specific way the collision invariant assigns its weights?

I computed the correlation between how large a collision coefficient is ($|\hat{S}^\circ(\chi)|$) and how large the corresponding prime sum is ($|P(0.5, \chi)|$) across all odd characters. If these were independent, the correlation would hover near zero.

```
base    odd chars    correlation
----    ---------    -----------
  3         3           +0.00
  5        10           -0.45
  7        21           -0.28
 11        55           -0.23
 13        78           -0.27
 17       136           -0.32
 19       171           -0.13
 23       253           -0.26
 29       406           -0.24
 31       465           -0.24
 37       666           -0.27
```

Negative. At every base. From three characters to six hundred and sixty-six. The correlation never crosses zero.

Characters with large collision coefficients have small prime sums. Characters with large prime sums have small collision coefficients. The collision invariant and the prime distribution are avoiding each other in character space.

Now think about what the prime character sum $|P(s, \chi)|$ actually measures. Through the relation $P = \log L - H$, it is a proxy for how sensitive that character is to the zeros of its $L$-function. Characters with large $|P|$ are the ones most affected by nearby zeros. They are the tremor-sensitive instruments in the array.

And the collision invariant puts its smallest weights on exactly those characters. It puts its largest weights on the characters that barely feel the zeros at all.

In the tested bases, the digit function $\lfloor br/p \rfloor$ produces a spectral profile that is transverse to the zero-sensitive directions in character space. The data suggests the instrument is not looking directly at the zeros. It is looking past them. If that holds up, the sum converges not because the zeros are absent, but because the instrument is pointed somewhere else.

## The scramble

A correlation table is suggestive. It is not proof. I needed something harder. So I asked a simple question. If the specific pairing between coefficients and characters is what makes the sum converge, what happens if I break the pairing?

Imagine an orchestra. Twenty instruments, twenty parts. The music works because each instrument plays the part written for it. Now shuffle the sheet music randomly across the stands. Same instruments. Same notes on the pages. Same musicians. But the oboe is reading the cello part, the violin is reading the timpani part, and nobody is playing what was written for them.

The music falls apart.

I did the mathematical version of this. I took the twenty collision coefficients and the twenty character sums in base $10$ and randomly shuffled which coefficient goes with which character. Same ingredients, different assignment. I computed the net sum. Then I did it again. And again. Ten thousand times.

```
base    actual net    scrambled mean    scrambled std    z-score
----    ----------    --------------    -------------    -------
  7       +1.81           -0.16             0.92          +2.1
 13       +3.45           -0.05             1.43          +2.5
 19       +5.11           -0.07             1.66          +3.1
 29       +5.32           +0.02             2.09          +2.5
 31       +6.73           -0.00             2.27          +3.0
```

The scrambled average lands near zero. Every time. The actual net, the one produced by the collision invariant's natural assignment, sits two to three standard deviations above, alone at the top. Ten thousand random shuffles, and none of them come close to what the digit function does on its own.

In the tested bases, the convergence is not just a property of the ingredients. It is a property of the arrangement. The collision invariant does not just have the right coefficients and the right characters. It has the right coefficients paired with the right characters. Shuffle the pairing and the positive net collapses to noise. The music was in the orchestration.

## What came through the door

I started this program because a digit function had a structural constant that matched the golden ratio. I followed the collisions to a periodic table, the periodic table to a transform, the transform to a convergence at $s = 1$, the convergence to a door into the critical strip. At every step I told myself the destination was the Riemann Hypothesis, and at every step I wanted that to be true more than I was willing to admit. That was the mountain everyone was climbing. I thought the collision transform was a new route up the same face.

It is not.

The collision transform does not test each $L$-function individually. The signs are mixed. In the data, the instrument looks past the zeros. The orchestration, not just the notes, is what makes the net positive. If $F^\circ$ converges at $s = 1/2$, the statement is not that every odd $L$-function modulo $m$ has its zeros on the critical line. The statement is that the zeros, wherever they sit, are arranged so that their effects cancel under the collision weighting. Not a statement about the emptiness of the zero set. A statement about its geometry.

I had been climbing a mountain and discovered it was a different mountain.

That is not a disappointment. A collective constraint on the joint zero distribution of a family of $L$-functions is not a lesser result than GRH. It is a different kind of result, one that the classical tools are not designed to see, because the classical tools work one $L$-function at a time. The collision transform works on all of them at once, weighted by the digit geometry, and what it sees is the shape of their arrangement.

I do not yet have a proof that the anti-correlation is structural. I do not know why the digit function $\lfloor br/p \rfloor$ produces Fourier coefficients that are transverse to the zero-sensitive directions. The scramble test says the orientation is real in the data. The computation leaves very little room for coincidence. But the proof says nothing yet about why.

That is where this paper leaves the story. The door is open. What came through was not what I expected. It may be more interesting.

## A note from 2026

*April 2026*

The general neutrality theorem entered [The Collision Transform](https://arxiv.org/abs/2604.00047) preprint as the foundation for the sieve-like argument that the centered sum is constrained at every prime scale. The simultaneous neutrality corollary became one of the structural pillars of the conditional penetration result.

The sign structure and anti-correlation did not become theorems. They remain computational observations, clearly labeled as such in the preprint. But they changed the direction of the program. Before this paper, I thought convergence of $F^\circ$ at $s = 1/2$ would be equivalent to GRH. After this paper, I understood it could not be. The mixed signs mean the collision transform can absorb individual $L$-function zeros through cancellation between terms. The convergence constrains the joint zero distribution, not each $L$-function individually. That distinction turned out to be fundamental.

Proving that the anti-correlation is structural remains the deepest open question in the program. It would require understanding why the digit geometry produces Fourier coefficients transverse to the zero-sensitive directions. The scramble test says the orientation is real in the data. The proof says nothing yet about why.

.:.

---

## Try it yourself

This post has three discoveries in it. Here they are, one command at a time.

**Discovery 1: neutrality holds at every prime.** Run this and check the last column. If the general neutrality theorem is true, every row should read zero. It does. Try raising `--qmax` to $37$ or higher. Still zero.

```
$ ./nfield general_neutrality 10 --lag 1 --qmax 19
```

**Discovery 2: the signs are mixed.** This shows the character-by-character products that make up $F^\circ$. Count the positives and the negatives. If they were all positive, this would be a GRH test. They are not all positive. Look at the magnitudes. The positive terms are *larger*, not more numerous. That is why the net is positive.

```
$ ./nfield sign_structure 10 --lag 1
```

**Discovery 3: the arrangement matters.** This is the scramble test. It shuffles the coefficients across the characters ten thousand times and compares the scrambled nets to the actual net. The scrambled average should land near zero. The actual net should sit well above it. If it does, you are seeing evidence that the anti-correlation is carried by the pairing, not just the parts.

```
$ ./nfield scramble_test 10 --lag 1 --trials 10000
```

Finally, sweep across prime bases and watch the Pearson correlation between coefficient size and prime sum size. It should be negative at every base. In the data, the collision invariant puts its weight where the zeros are quietest.

```
$ ./nfield anticorrelation_sweep --lag 1 --bmax 37
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The General Neutrality Theorem](https://github.com/alexspetty/nfield/blob/main/research/general_neutrality.pdf)

---

*Alexander S. Petty*
July 2024 (updated April 2026)
.:.
