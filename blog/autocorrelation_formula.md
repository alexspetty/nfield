# The Autocorrelation Formula

There was one place in the chain where the gears didn't quite mesh.

Take $1/7$ in base $10$. The repeating loop is $142857$. Slide it by one and lay the slid copy under the original.

```
1 4 2 8 5 7
4 2 8 5 7 1
```

Zero matches. Slide by two, three, four, five. Same answer every time.

```
shift:    1  2  3  4  5
matches:  0  0  0  0  0
```

Five shifts, five zeros. The loop of $1/7$ refuses to line up with any shifted copy of itself at any position. That row of zeros is a fact about the prime $7$, and it does not generalize. At other primes the row is not all zeros. The loop of $1/29$ matches itself at three or four positions out of twenty-eight at certain shifts. The loop of $1/41$ has its own pattern. Each prime has its own profile of self-agreement under shifting.

That profile is the load-bearing data of an entire chain of formulas. Run it through a discrete Fourier transform and you get the eigenvalues of the prime, the harmonic content of its field of fractions $1/p, 2/p, 3/p, \ldots$ at a depth that the prime's other invariants do not reach.

The chain from the self-match counts to the eigenvalues had every step in closed form. Every step except one. The counts themselves had no formula. To get them, I had to write out the loop, slide it, and compare, position by position. The whole chain was arithmetic except for that one place, and that one place was patience. It was the gear that didn't mesh.

This paper finds the missing formula. The self-match counts come out of the structure of the prime alone, without ever doing the long division.

## What loudness cannot see

Before this paper, I already had a way to measure how loud the prime is at each harmonic. [The spectral power paper](https://alexpetty.com/the-spectral-power-of-the-digit-function/) gave me a function, computable from a few elementary things about the prime, that records the loudness profile across all frequencies. I had hoped that profile would be enough to compute the self-match counts.

It is not. The reason is the same reason loudness alone cannot tell you whether two waves cancel when you add them up.

Imagine two waves of identical loudness. One peaks at the start of each second. The other peaks in the middle. Their loudnesses are the same. But if you lay them on top of each other, the first wave's peaks fall on the second wave's troughs, and the sum is zero. The waves cancel each other and disappear. Now imagine instead that the second wave peaks at the start of each second too, in step with the first. The waves stack instead of canceling, and the sum is twice as loud. Same loudness in both cases, completely different result.

The difference between cancellation and reinforcement is timing. Loudness alone cannot see timing. To predict cancellation or reinforcement, you need a richer measurement that records *when* the peaks fall, not just how high they reach.

The self-match counts of a prime have exactly the same structure. They depend on whether the prime's harmonic content is in step or out of step at related frequencies. The loudness profile tells me how strong each frequency is. It does not tell me when each frequency peaks. To recover the self-match counts, I needed an object one rung up from loudness, an object that kept the timing as well as the loudness.

## One step richer

The fix turned out to be mechanical, and the result was one of those upgrades that feels obvious once you have it in front of you.

Instead of recording one number per frequency, record one number per *pair* of frequencies. The result is a two-dimensional table. The rows and columns are indexed by frequencies. Each entry of the table holds the joint timing-and-loudness information of the prime at that pair of frequencies.

I will call the table $G$ once, here, so the formula at the end has a name to point at. You do not need to remember the letter. Stay on the surface with me. The diagonal of the table is the loudness profile that I already knew. The off-diagonal entries are new. They are the timing information that the loudness profile threw away. The table has more in it than the loudness alone, exactly enough more to count self-matches.

I want to claim that the self-match count at any given shift is a sum of entries from the table along a particular path. Different shifts trace different paths through the same table. To prove the claim, I need one small fact about the table, and the fact is so quiet that you could pass over it the first time you see it without noticing.

## A small fact that does big work

The fact is this. **If you add up every entry in the table, the result is exactly zero.**

The reason is obvious once you understand it. Each entry of the table is built out of pieces, and each piece is a sum of waves spaced evenly around a circle. Evenly spaced waves around a circle always cancel. Every piece vanishes for that one reason, and the whole table vanishes in the aggregate.

It does not look like a useful fact. It looks like a footnote. Hold onto it anyway.

## The collapse

Here is where everything has been heading.

Start with what the count actually is. At a given shift, the self-match count asks how many residues have the same digit at their original position and at their shifted position. Write that as one big sum, one term per residue, where the term is a $1$ when the two digits agree and a $0$ when they do not.

The first move is to break the agreement test open. Two digits agree exactly when there is some bin they both land in. So the agreement test becomes a sum over bins of a paired bin check, did this residue land in this bin, and did its shifted partner land in the same bin. The count is now a double sum: one layer over residues, one layer over bins.

The second move turns counting into harmonics. Every bin indicator, the function that says "yes you're in this bin" or "no you're not", can be rewritten as a sum of waves on the circle of $p$ residues. Substitute that rewriting into both bin checks. The sum over residues folds up into a wave sum, and what is left is a double sum over pairs of frequencies, with each pair weighted by an entry of the table from before. In schematic form,

$$R(\ell) = \sum_{\text{pairs of frequencies}} (\text{table entry}) \cdot (\text{wave sum at the combined frequency}).$$

The wave sum is the small object we already met. It takes one of two values. If the combined frequency is zero on the circle of $p$ residues, the waves all line up and the sum is the large positive number $p - 1$. Otherwise the waves cancel and the sum is the small negative number $-1$. Two values, exactly as advertised.

So every pair of frequencies pays one of two prices, and the count splits cleanly into two pieces,

$$R(\ell) = (p - 1) \cdot (\text{sum of table entries on the diagonal}) - (\text{sum of table entries off the diagonal}).$$

The "diagonal" here is the set of pairs whose combined frequency is zero, the path the shift carves out across the table. The "off-diagonal" is everything else. Two unknown sums, one equation. It looks bad.

And here, finally, the small fact walks on stage. The whole table sums to zero. Every pair lives in exactly one of the two camps. So the two camp sums must be equal and opposite. Whatever the off-diagonal sum is, it is exactly the negative of the on-diagonal sum.

That single observation eats half the formula.

Substitute. The minus sign in front of the off-diagonal sum turns into a plus. The two camps merge into one. The whole expression compresses to a single walk along the diagonal,

$$R(\ell) = \frac{1}{p} \cdot (\text{sum of table entries along the diagonal the shift carves out}).$$

That is the autocorrelation formula. The self-match count at any shift is one walk along one diagonal of the table, divided by the prime. The dense expansion, the two warring camps, the long sum over pairs, all of it has compressed into one walk along one path.

The first time you watch this happen it looks like a trick. Two completely unknown sums, locked together by a single throwaway identity, fold into each other and out pops a closed formula. After sitting with it for a while the trick starts to feel like something else. The two camps are equal and opposite not because we are lucky but because the prime has exactly $p$ residues, and the harmonics over $p$ residues are forced to balance around the circle. The collapse is not a coincidence I exploited. It is the prime telling me what shape it is. I am just transcribing.

## Watching it work at $p = 7$

Time to go back to $p = 7$ and watch the formula reproduce the string of zeros from the opening, step by step, with no hand waving.

In base $10$, the loop of $1/7$ is

```
1/7 => 0.|142857|
```

Six digits, all different. Each digit shows up exactly once in the loop. So the six bins of the digit function (the groupings of residues that share a digit) are all the same size, one residue apiece. The bins of $7$ in base $10$ are perfectly uniform.

That uniformity is what makes the table for $p = 7$ so well-behaved. When the bins are all the same size, the table only ever takes two values. Most of its entries are the small negative number $-1$. Seven of them, sitting on one particular line of the table, are the large positive number $6$. Forty-two minus ones and seven sixes. That is the entire table for $p = 7$.

Now pick the shift of one position. The diagonal the shift carves out is a walk through seven entries of the table, one entry per frequency. Of those seven entries, exactly one of them falls on the line of $6$s and the other six fall on the field of $-1$s. So the path picks up the values

```
6, -1, -1, -1, -1, -1, -1
```

Add them up. $6 + 6 \cdot (-1) = 0$. Divide by $p = 7$. The self-match count at shift one is exactly $0$. The formula has reproduced the first zero from the opening.

Now do it again for shift two. The path is a different walk through the table, picking up a different combination of seven entries. But again exactly one of them lands on the line of $6$s and the other six land on the field of $-1$s. Total: zero. Repeat for three, four, five. Same outcome every time.

```
shift:     1  2  3  4  5
path sum:  0  0  0  0  0
R(shift):  0  0  0  0  0
```

Five shifts, five walks through the table, five zeros, every one verified by hand against the row of zeros at the top of this paper. I never wrote down the digits of $1/7$ to get them. I never sliced the loop or compared it to a shifted copy. I built the table from the bin sizes, walked the seven entries the shift picked out, and added the numbers. The arithmetic was simpler than the long division would have been.

This is what closing the chain feels like. The bin sizes go in. The table is built. The paths are walked. The self-match counts fall out. The eigenvalues fall out of those. Every step is finite arithmetic. At no point do I have to look at the digits of $1/p$.

## The hole that remains

The argument above works at primes where the base $10$ generates the full multiplicative structure modulo $p$. That technical condition is what makes the cancellation exact. At primes where the base $10$ does not generate the full structure (the multi-coset primes), the same trick fails. The table walks through a smaller world, and the simple cancellation that worked above no longer carries through cleanly.

The fix needs another layer of harmonic analysis sitting on top of the one used here. That generalization is not in this paper. It is the next problem in the chain, and my current plan is to take it up next. For now, the formula closes the chain at most primes, and I hope that "most" will turn out to be enough to make the rest of what I want to do go through.

## A note from 2026

*April 2026*

The cancellation that powers this paper turned out to be the structural ancestor of a move that runs through the entire program. Every time a centered Fourier sum collapses two pieces into one because the trivial-character contribution was killed by a centering identity, the underlying mechanism is the small fact about $G$ from this paper. The collision invariant program at conductor $b^2$ uses an analogous identity to force the trivial coefficient of the collision invariant table to be exactly $-1/2$, and the [collision transform](https://alexpetty.com/the-collision-transform/) builds its Mertens-style cancellation argument on a centering identity that has the same shape as the one used here. Different signal, different group, same move.

The two-variable table $G$ also generalizes. In the [collision spectrum](https://alexpetty.com/the-collision-spectrum/), the collision invariant table at conductor $b^2$ is decomposed over the Dirichlet characters modulo $b^2$, and a two-variable correlation table plays the role of $G$ for that program. A one-variable invariant (the loudness here, the variance there) is always the diagonal of a two-variable invariant, and the off-diagonal always carries the deeper information. Once you have learned to look for the off-diagonal, you start finding it everywhere.

The closing of the chain at this paper, the moment when every arrow becomes explicit, was a small declaration of what kind of program this is. The alignment program is computational at every step. There is no point in the chain where a quantity is defined only through limits or only through existence theorems. Bin sizes are arithmetic. The harmonic pieces are trigonometric. The self-match counts are finite character sums. The eigenvalues are a finite Fourier transform. Everything at this level can be handed to a calculator and verified by hand at small primes. That property survived into every later chapter of the program, and it is what made the eventual leap to $L$-functions tractable. By the time the analytic machinery enters, every quantity it touches has already been built explicitly from below.

.:.

---

## Try it yourself

```
$ ./nfield autocorrelation 7
  R(0) = 6
  R(1) = R(2) = R(3) = R(4) = R(5) = 0
  formula matches direct count: yes

$ ./nfield autocorrelation 29
  R(0) = 28
  R(1)..R(27): values from 0 to 4
  formula matches direct count: yes

$ ./nfield autocorrelation 41
  R(0) = 40
  rich self-match profile, all values verified
```

At $p = 7$ the self-match count is the all-zeros pattern that the long-division check predicts. At $p = 29$ the count is small but nonzero at several shifts, and the formula reproduces every value. By $p = 41$ the count has real internal structure, and the eigenvalues that come out of it have the spread you would expect from a prime where the digit bins are crowded.

The thing to notice in the demos is that the verification happens twice. Once by counting digit matches the slow way, by long division and comparison, and once by walking the paths through the table. The two answers agree. Before the formula, only one of those two methods existed. After the formula, the slow way is a check on the fast way, not the only way to know the answer.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Autocorrelation Formula](https://github.com/alexspetty/nfield/blob/main/research/autocorrelation_formula.pdf)

---

*Alexander S. Petty*
January 2022 (updated April 2026)
.:.
