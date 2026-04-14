# Bin Derangements and the Gate Width Theorem

## Forget the prime

Nine. At every prime in base ten, this is the number of multipliers that move every digit out of its original bin. Nine at $p = 13$. Nine at $p = 1009$. Nine at $p = 10{,}007$. Nine at every prime in the universe past the base, no matter how large the prime gets, no matter what other properties it has.

The count depends on the base and nothing else. In base ten the answer is nine because nine is one less than ten. In base seven the answer is six. In base three the answer is two. In base $b$, the answer is always exactly $b - 1$. Nothing about the prime enters at all.

The first time I noticed this, I assumed it was a coincidence that would break at the next prime I tried. It did not. The first time I tried to prove it, I assumed the proof would lean somewhere on the multiplicative structure of $p$. It did not need to. The result holds at every prime past the base, and the proof goes through a single change of variables that turns the geometry of the digit bins into the algebra of residue classes. That move is the spine of this paper, and I will walk through it after the experiment that drove me to look for it.

Pick a prime $p$ and a base $b$. Each residue $r$ between $1$ and $p - 1$ wears a digit, the leading digit of the decimal expansion of $r/p$. Residues that wear the same digit live in the same *bin*.

At $p = 13$ in base $10$, the twelve residues split into ten bins. Eight of them hold a single residue. Two of them are crowded. Bin $3$ holds residues $4$ and $5$, because both $4/13 = 0.307\ldots$ and $5/13 = 0.384\ldots$ begin with the digit $3$. Bin $6$ holds residues $8$ and $9$, because both $8/13 = 0.615\ldots$ and $9/13 = 0.692\ldots$ begin with the digit $6$. The crowded bins are going to be where all the interesting things happen.

Now multiplication. For any nonzero $g$ between $2$ and $12$, the map $r \mapsto gr \bmod 13$ permutes the residues. For most choices of $g$, every residue lands in a new bin. For some choices, a residue or two stays stuck in its original bin. The question I started watching is how often each happens.

I worked out the full check at $g = 10$. Here is the entire result in one table: the residue, its fraction, the residue after multiplication by $10$, that residue's fraction, and whether the two share a leading digit.

```
 r    r/13      gr    gr/13     same leading digit?
--   --------   --   --------   -------------------
 1    0.0769    10    0.7692           no
 2    0.1538     7    0.5384           no
 3    0.2307     4    0.3076           no
 4    0.3076     1    0.0769           no
 5    0.3846    11    0.8461           no
 6    0.4615     8    0.6153           no
 7    0.5384     5    0.3846           no
 8    0.6153     2    0.1538           no
 9    0.6923    12    0.9230           no
10    0.7692     9    0.6923           no
11    0.8461     6    0.4615           no
12    0.9230     3    0.2307           no
```

Twelve residues, twelve new fractions, zero shared leading digits. You can scan down the second and fourth columns and see for yourself that no two entries on the same row begin with the same digit. Multiplication by $g = 10$ moves every residue out of its original bin. The map deranges the bin structure completely.

Now do the same experiment for every other choice of $g$ from $2$ to $12$, count the collisions in each case, and summarize. Here is the entire experiment for $p = 13$ in one table.

```
 g     collisions   deranging?
--    -----------   ----------
 2          0           yes
 3          0           yes
 4          0           yes
 5          0           yes
 6          2           no
 7          0           yes
 8          0           yes
 9          0           yes
10          0           yes
11          2           no
12          0           yes
```

Eleven rows. Nine zeros. **Nine.**

The two non-zero rows are $g = 6$ and $g = 11$. At $g = 6$, residue $5$ lands at $gr = 4$, and both $5/13$ and $4/13$ begin with the digit $3$, so residue $5$ stays in bin $3$. Residue $8$ lands at $gr = 9$, both fractions begin with $6$, residue $8$ stays in bin $6$. Two stuck, ten move. Not a derangement. The same thing happens at $g = 11$, with residues $4$ and $9$ stuck in those same two bins instead of $5$ and $8$.

Nine deranging multipliers at $p = 13$. Now scale up.

Take $p = 29$. Twenty-seven non-identity choices of $g$.

Nine.

Take $p = 83$. Eighty-one choices.

Nine.

Take $p = 1009$. A thousand and seven choices.

Nine.

The choices of $g$ grow linearly with the prime. The count of deranging multipliers does not grow at all. Nine, every prime in base ten, forever. This paper is about why.

## The gate width theorem

Strip the experiment back to a clean statement.

**Theorem (informal).** *Take a prime $p$ larger than the base $b$. The number of multipliers that derange the bin structure is exactly $b - 1$. In base ten, that means nine. In base seven, six. In base three, two. The count never depends on the prime.*

A word about where this sits. The proof, which I will walk through in the next few sections, uses nothing more advanced than the Euclidean algorithm and a short counting argument. The techniques are elementary. The bins of the digit function have been studied for over a century, and the Beatty-partition structure of their sizes goes back to the three-distance theorem of Sós in 1958. What I have not been able to find anywhere is the specific question of how multiplication by a fixed nonzero residue scrambles those bins. The bins exist in the literature as a byproduct of studying how digits of fractions distribute, not as an object whose multiplicative behavior is itself interrogated. The result of this paper is what falls out when you do interrogate it. If a specialist points me at a citation where this has already been written down, I will fold it in gladly. The reason the paper exists despite using only elementary techniques is that the result is load-bearing for the longer chain that depends on it.

There are a handful of reasons the answer still feels surprising once you have seen it. Let me list them, because the surprise is sharper if you can see what the count was supposed to depend on.

The bin pattern is complicated and varies wildly across primes. At $p = 11$ in base $10$ each bin has either zero or one residue. At $p = 23$ some bins have two residues and others have three. At $p = 1009$ some bins have a hundred residues and others have a hundred and one. There is no obvious reason that a count of derangements should look past all that variation.

Then there is the primitive root problem. At some primes the powers of the base $b$ run through every nonzero residue mod $p$ before they cycle back. The base *generates* the whole multiplicative group. At other primes the powers of $b$ cycle through only a smaller subset and miss most of the residues. The two cases are not rare versus rare. In base $10$, only about $37\%$ of primes have $10$ as a primitive root. The other $63\%$ have a short orbit that misses more than half the residues.

This mattered enormously in the earlier papers in this chain. The autocorrelation of the repetend of $1/p$ lives on the orbit of $b$, so when the orbit is short, the autocorrelation cannot see most of the multiplicative group. Every result in [the autocorrelation formula](https://alexpetty.com/the-autocorrelation-formula/) and [phase-filtered Ramanujan sums](https://alexpetty.com/phase-filtered-ramanujan-sums-and-the-spectral-gate/) was implicitly restricted to primes where $b$ is a primitive root. That restriction silently excluded most of the primes I cared about.

The gate width theorem drops the restriction. The proof works on the digit function directly, never touching the orbit, never needing the powers of $b$ to generate anything. It applies at every prime past $b + 1$, primitive root or not. The majority of primes that the earlier papers were silent about are back in the picture.

Even the spectral classes from [phase-filtered Ramanujan sums](https://alexpetty.com/phase-filtered-ramanujan-sums-and-the-spectral-gate/), which sort primes into $\varphi(b)$ families by their last digit, do not help here. Two primes from different spectral classes still produce the same number of derangements. The classification controls *which* multipliers are deranging. It does not control *how many*.

Every sensible prediction says the count should depend on at least one of these things. None of them matter. The count is set by the base alone.

## The trick that linearized everything

The reason the result feels surprising, and the reason it took me a while to find a proof, is that the bins do not look algebraic. They are *intervals*. Bin $0$ is the residues whose leading digit is $0$, which means they sit at the start of $\{1, \ldots, p - 1\}$. Bin $1$ is the next slab. Bin $2$ the next. The bins are contiguous chunks of the residues, and the chunk lengths depend on the prime in an irregular way.

Contiguous chunks resist almost every tool I know. Fourier analysis is the wrong language for them, because their indicator functions have ugly Fourier coefficients. Group theory is the wrong language because they are not subgroups. Combinatorial bijections are the wrong language because there is no symmetry in the chunk sizes.

Every direct attack I tried fell apart. The argument that finally worked goes through a single change of variables that is so clean it is almost embarrassing.

Here it is. Take any residue $r$. Multiply it by the base $b$, take the answer modulo $p$, and call the result $x$. The map $r \mapsto x$ is a permutation of $\{1, \ldots, p - 1\}$, since $b$ is invertible mod $p$. So the rule "shuffle the residues by multiplying by $b$" reorganizes the same set into a different order.

What does the shuffle do to the bins? In the old coordinates, bin $d$ was the residues whose leading digit equals $d$. In the new coordinates, bin $d$ becomes the residues with $x \equiv d \pmod{b}$.

Read that twice. The contiguous interval of residues whose digit is $d$ in the old coordinates becomes the residue class of integers congruent to $d$ modulo $b$ in the new coordinates. The bins, which were complicated geometric chunks, are now simple residue classes. The geometry has turned into algebra, in one move.

I sat with this for a long time when I first noticed it. It is the kind of move that is obvious in retrospect and impossible to reverse-engineer. Some part of the structure of the problem was being expressed in the wrong coordinates the whole time, and the right coordinates had been one multiplication away.

Once you are in the right coordinates, the deranging question becomes easy. "Does multiplication by $g$ scramble all the bins?" becomes "is there any $x$ for which $x$ and the result of multiplying it by $g$ land in the same residue class mod $b$?" That is a one-line linear question. The answer comes out in a few lines of calculation, and the calculation gives you the gate width theorem.

## The squeeze

Once the question is linear, it reduces to a small geometric inequality. Let me walk through it without notation overload.

Define a single number that depends only on $g$ and the base. Call it $c$. Its formula is $c = b/(1 - g) \bmod p$, which is just one division in the residues mod $p$. This number turns out to be the only thing that matters. The question of whether $g$ is deranging reduces entirely to where $c$ lives between $1$ and $p - 1$.

Here is the picture. You have two arithmetic progressions inside $\{1, \ldots, p - 1\}$. The first progression takes steps of size $b$. The second takes steps of size $c$. A collision happens when these two progressions land at the same residue at the same step number. No collision happens when they cannot.

The squeeze is this. If $c$ is small (between $1$ and $b - 1$), the second progression takes steps that are too small to ever catch up to the first. The two progressions always maintain a gap, and no collision is possible. If $c$ is large enough (at least $b + 1$), the second progression takes steps that overshoot, and you can construct a collision explicitly.

The deranging multipliers are exactly the ones whose $c$ lands in the small range $\{1, 2, \ldots, b - 1\}$. There are $b - 1$ such values of $c$. Each one gives a different $g$. That is the count, and it does not depend on the prime, because the small range $\{1, \ldots, b - 1\}$ does not depend on the prime.

Reverse the substitution. From $c = b/(1 - g)$ we get $g = 1 - b/c$. Setting $u = b - c$ for cleaner indexing, the deranging multipliers are

$$g = -\frac{u}{b - u} \pmod{p}, \qquad u = 1, 2, \ldots, b - 1.$$

Nine values when $b = 10$. Six when $b = 7$. Two when $b = 3$. Always $b - 1$.

## Nine numbers for $p = 13$

The formula is general, but it is only believable once you have computed it for one prime by hand. Plug $p = 13$ and $b = 10$ in, grind through the modular arithmetic for each value of $u$, and here is what comes out.

```
u =  1   g = -1/9  (mod 13)  =  10
u =  2   g = -1/4  (mod 13)  =   3
u =  3   g = -3/7  (mod 13)  =   7
u =  4   g = -2/3  (mod 13)  =   8
u =  5   g = -1/1  (mod 13)  =  12
u =  6   g = -3/2  (mod 13)  =   5
u =  7   g = -7/3  (mod 13)  =   2
u =  8   g = -4/1  (mod 13)  =   9
u =  9   g = -9/1  (mod 13)  =   4
```

Sorted, the nine deranging multipliers at $p = 13$ in base $10$ are

$$\{2, 3, 4, 5, 7, 8, 9, 10, 12\}.$$

Nine values, exactly as the theorem promises. The two non-trivial residues that are *not* in this list are $6$ and $11$, the same two multipliers we found by hand at the very start of this paper, the ones that left two residues in their original bins.

## The complement and the inverse pairs

The deranging set has internal symmetries that are worth seeing.

The middle entry, $u = 5$, gives $g = -1$, which is $12 \pmod{13}$. This is the *complement element*, the multiplier that sends every residue $r$ to $p - r$. In base $10$ it is what people sometimes call the "nines complement". Whenever the base is even, $u = b/2$ falls in the deranging set, and the complement is automatically a derangement. The nines complement is the most familiar derangement that nobody had a name for.

The other eight derangers come in pairs that are mutual inverses mod $p$. The pairs follow $u \leftrightarrow b - u$:

```
u = 1 ↔ u = 9    g = 10 and g = 4    10 · 4 = 40 ≡ 1 (mod 13)
u = 2 ↔ u = 8    g =  3 and g = 9     3 · 9 = 27 ≡ 1 (mod 13)
u = 3 ↔ u = 7    g =  7 and g = 2     7 · 2 = 14 ≡ 1 (mod 13)
u = 4 ↔ u = 6    g =  8 and g = 5     8 · 5 = 40 ≡ 1 (mod 13)
u = 5            g = 12 (self-inverse: 12 · 12 = 144 ≡ 1)
```

Four pairs of inverses, plus the self-inverse complement, for a total of nine. The pairing is what the formula $g = -u/(b - u)$ encodes when you swap $u$ and $b - u$. The structure repeats at every prime in base ten. The pairs change identity from prime to prime, but the pair structure is invariant.

## Three regimes, one formula

The gate width theorem accounts for the multipliers that produce zero collisions. There are also $p - b - 1$ multipliers (in our running example $13 - 10 - 1 = 2$ of them, $g = 6$ and $g = 11$) that produce some positive number of collisions, and the natural follow-up question is whether those positive numbers themselves have any structure.

They do, and the structure is another closed formula. It depends on two integers that come from a single division. Write $p - 1 = bQ + R$, where $Q$ is the integer quotient and $R$ is the remainder. The number $R$ is the number of "large" bins (the ones that hold $Q + 1$ residues) and $b - R$ is the number of "small" bins (the ones that hold $Q$ residues). At $p = 13$ and $b = 10$, the division gives $12 = 10 \cdot 1 + 2$, so $Q = 1$ and $R = 2$, meaning two large bins and eight small bins. Sure enough, the bins of $13$ in base $10$ are $\{1\}, \{2\}, \{3\}, \{4, 5\}, \{6\}, \{7\}, \{8, 9\}, \{10\}, \{11\}, \{12\}$, two of them with two residues and the rest with one.

The average number of collisions over the constructive multipliers is

$$\overline{C} = \frac{Q \, (b(Q - 1) + 2R)}{b(Q - 1) + R}.$$

Three special cases bring the formula to life.

When $R = 0$ (primes in the spectral class that ends in $1$, like $11, 31, 41, 61, 101$), the formula collapses to $\overline{C} = Q$ exactly. The average collision count is exactly the bin size. At $p = 31$, $Q = 3$ and the average is $3$. At $p = 61$, $Q = 6$ and the average is $6$. Clean integers, every time.

When $Q = 1$ (the smallest primes past $b + 1$ in any spectral class, like $13, 17, 19, 23$ in base ten), the formula gives $\overline{C} = 2$. Always exactly two. The smallest primes in any class produce an average constructive collision of two, regardless of which class they belong to.

For large primes in any class, $Q$ is large and $R$ stays bounded by $b$, so $\overline{C} \approx Q \approx p/b$. The average constructive collision count grows linearly with the prime, at rate $1/b$.

Three regimes, three clean answers, all from one formula.

## Base counts, prime chooses

Together, the gate width theorem and the mean formula split the autocorrelation of a prime repetend into two independent halves.

The base controls the *count* of zero lags. There are exactly $b - 1$ deranging multipliers at every prime, no matter which prime you pick. This is a property of the coordinate system, not of the object you are observing.

The prime controls the *content* of the constructive lags. Which $b - 1$ multipliers happen to be deranging depends on the prime, but how many there are does not. The average collision intensity at the constructive lags has a closed form in $Q$ and $R$, and the distribution around the mean is the structural fingerprint of the prime itself.

This is the cleanest decomposition I have anywhere in the alignment program. The base contributes one dimension. The prime contributes the other. They do not interact at the level of counts. They only interact at the level of *which* multipliers do which thing.

## Paying off the orbit

The gate width theorem dropped a hypothesis I had been carrying around for some time. The phase-filtered Ramanujan sums result needed $b$ to be a primitive root mod $p$, which excluded a substantial fraction of primes in any base. The proof in this paper uses no such hypothesis, because it works on the digit function directly and never needs the multiplicative orbit at all.

That is a bigger shift than it sounds. Every later piece of the chain that builds on the gate width theorem is now unconditional in the prime, and that is what I want for the program. The dependence on hypotheses was a debt I had been carrying. Paying it off here means the foundation of the alignment program is anchored to the digit function, not to the orbit of the base. The orbit is a useful coordinate when you have it. The result does not need it.

## A note from 2026

*April 2026*

The gate width theorem turned out to be the structural anchor of everything that came later. The "two controls" framing introduced here, the idea that the base controls the count and the prime controls the content, became one of the central organizing principles of [the collision invariant](https://alexpetty.com/the-collision-invariant/). When I started building the collision invariant table at depth two, with $b^2$ residue classes instead of $b$, the same separation held. The base controls the count of derangements at every depth. The depth controls the resolution. The prime controls the family-by-family structure within.

The change of variables $r \mapsto br \bmod p$ that linearized the proof in this paper became the prototype of every later linearization in the chain. Every time I needed to turn a geometric statement about contiguous intervals into an algebraic statement about residue classes, I went back to this trick. The general version is what the [collision spectrum](https://alexpetty.com/the-collision-spectrum/) calls the bin character sum, and the seed of the bin character sum is here, in the conjugation lemma.

The mean formula bonus turned out to be more important than I realized at the time. The exact closed form $\overline{C} = Q(b(Q-1) + 2R)/(b(Q-1) + R)$ generalizes to a Parseval-style identity for the second moment of $|L(1, \chi)|^2$ over Dirichlet characters in [the collision spectrum](https://alexpetty.com/the-collision-spectrum/), and the special case $\overline{C} = Q$ for the spectral class $R = 0$ is the cleanest fingerprint anywhere in the program. I did not know in 2022 that these little arithmetic identities would feed into L-function moments. They did.

But the part of this paper that mattered most in retrospect was the dropping of the primitive-root hypothesis. Once the gate width theorem was unconditional in the prime, the rest of the chain could be unconditional too, and the alignment program became something that worked at every prime instead of at most primes. That is the upgrade this paper bought, and I did not realize at the time that I was buying it.

.:.

---

## Try it yourself

```
$ ./nfield derangements 13
  prime 13, base 10
  Q = 1, R = 2
  bins: {1} {2} {3} {4,5} {6} {7} {8,9} {10} {11} {12}
  deranging multipliers (9): {2, 3, 4, 5, 7, 8, 9, 10, 12}
  constructive multipliers (2): {6, 11}
  C(6) = 2, C(11) = 2
  mean over constructive: 2.00 (formula predicts 2.00) ✓

$ ./nfield derangements 29
  prime 29, base 10
  Q = 2, R = 8
  deranging multipliers (9)
  mean over constructive: 2.94 (formula predicts 2.94) ✓

$ ./nfield derangements 1009
  prime 1009, base 10
  Q = 100, R = 8
  deranging multipliers (9)
  mean over constructive: 100.16 (formula predicts 100.16) ✓
```

Three primes, three values of $Q$ and $R$, three averages. The deranging count is nine in every case. The mean formula matches exactly at every prime, even when the constructive count grows into the hundreds. Pick any prime past base + 1 and watch the same two numbers fall out.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [Bin Derangements and the Gate Width Theorem](https://github.com/alexspetty/nfield/blob/main/research/bin_derangements.pdf)

---

*Alexander S. Petty*
July 2022 (updated April 2026)
.:.
