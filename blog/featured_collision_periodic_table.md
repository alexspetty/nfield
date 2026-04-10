# The Collision Periodic Table

In 1869, Mendeleev arranged the known elements into a grid. Each element had a weight, a valence, a set of chemical properties. The grid organized them. Gaps in the grid predicted elements that had not yet been found. The periodic table turned chemistry from a catalog into a science.

The collision invariant does something similar for primes.

The first three papers ([A](https://arxiv.org/abs/2604.00045), [B](https://arxiv.org/abs/2604.00047), [C](https://arxiv.org/abs/2604.00054)) in this series proved that the collision invariant, a signed integer measuring how the digit function $\lfloor br/p \rfloor$ distributes remainders into bins, depends only on the last two digits of the prime. Not approximately. Exactly. The prime 10007 and the prime 40007 have the same collision value, because they both end in 07. The prime 10009 and the prime 990009 have the same collision value, because they both end in 09.

That means there is a table. Every base has one. Base 3 has 6 entries. Base 7 has 42. I work in base 10 because it is familiar, but the structure is not about base 10. The base is a lens. Different lenses give different tables, but they are all looking at the same thing; the arithmetic of the primes, which does not depend on how we write them down.

In base 10, the table has 40 entries:

```
       0   1   2   3   4   5   6   7   8   9
 0:    .   0   .  +2   .   .   .   0   .  +8
 1:    .  -1   .  -1   .   .   .  +1   .  -1
 2:    .   0   .  -2   .   .   .  +6   .   0
 3:    .  -1   .  -1   .   .   .  -3   .  -1
 4:    .  -4   .   0   .   .   .  -2   .   0
 5:    .  -1   .  +1   .   .   .  -1   .  +3
 6:    .   0   .  +2   .   .   .   0   .   0
 7:    .  -1   .  -7   .   .   .  +1   .  -1
 8:    .   0   .  -2   .   .   .   0   .   0
 9:    .  -9   .  -1   .   .   .  -3   .  -1
```

Row is the tens digit, column is the units digit. Dots mark classes that share a factor with 100. Every prime larger than 100 maps to exactly one cell. A table lookup replaces a computation.

The grid is not random. It is antisymmetric; the entry at 09 is +8, the entry at 91 is -9. Their sum is -1. Every complement pair, without exception, sums to -1. The mean across the whole table is $-1/2$. Not approximately. The number $-1/2$, exactly. It traces to the same parity structure in Dirichlet characters that gives rise to the functional equation of L-functions.

## The cancellation

Look at the table. The entries range from -9 to +8. Some cells are positive. Some are negative. Zero is a common value, +8 and -9 are the extremes.

Now imagine the primes arriving, one after another, each one landing in exactly one cell. The prime 109 lands at 09 and carries value +8. The prime 191 lands at 91 and carries value -9. The prime 10007 lands at 07 and carries value 0. An endless stream of primes, each handing over a signed integer as it passes.

Keep a running total. Does it climb? Does it fall? Does it balance?

The classical theory tells you the primes are evenly distributed across the cells; in the long run, each class gets its fair share. So the running total depends on whether the positive and negative entries cancel when weighted equally. An unweighted sum of the table gives $-1/2$ per cell. But the running total centers on that mean, not on zero. Subtract the mean and you get a new quantity, a centered collision value, whose expected contribution is zero. The question becomes a simple one. Does the centered sum actually hit zero, or does it drift?

It cancels. At the prime number theorem rate:

<div>
$$\sum_{p \le x} S_{\text{centered}}(p) = O\!\left(x \exp(-c\sqrt{\log x})\right)$$
</div>

The positive fluctuations and the negative fluctuations destroy each other. The main term is zero. The collision invariant, a quantity built from long division, cancels across primes at the same rate that the prime counting function approaches the logarithmic integral.

My proof uses no new analytic machinery. It cannot; the analytic theory of prime distribution is over a century old and thoroughly worked. The bridge between my collision invariant and that classical theory is the [decomposition theorem](https://arxiv.org/abs/2604.00054), a result I built in the previous paper to write the centered collision value as a finite sum of Dirichlet characters modulo $b^2$. Character sums over primes are classical; their cancellation is in every textbook. My contribution here is the identification of the collision invariant as a specific linear combination of those characters. Once that identification is made, the classical machinery does the rest.

## The clean constant

There is a caveat attached to the classical prime number theorem for arithmetic progressions, and it has lived there for a century.

The caveat is a hypothetical zero. Nobody has ever found one. Nobody has ever proved they cannot exist. For certain moduli, a real primitive Dirichlet character might have a zero of its L-function sitting unusually close to $s = 1$. This is called a Siegel zero. If one exists at your modulus, the error constant in the prime number theorem for that modulus becomes *ineffective*; you can prove the primes balance across residue classes, but you cannot say how fast, because the rate depends on a quantity no one has been able to rule out.

A century of work has not removed this asterisk. It is one of the hardest obstructions in analytic number theory.

The collision periodic table has no such caveat. Its modulus is $b^2$, a perfect square. For any base $b \geq 3$, the structure of a perfect-square modulus eliminates the exceptional character that a Siegel zero would require. The obstruction vanishes, not because of a hard analytic argument, but because the modulus is the wrong shape for it to exist.

I did not engineer the modulus to avoid Siegel zeros. I was not thinking about Siegel zeros at all. The modulus $b^2$ emerged from the digit function; the collision invariant depends on two base-$b$ digits, so it lives modulo $b^2$. It happens that this is exactly the shape of modulus the century-old obstruction cannot reach.

This is the deeper thing my contribution does. It takes a prime-distribution question that the classical framework can state but cannot always bound effectively, and it gives an effective bound, unconditionally, for every base. The constant $c$ in the error term $x\exp(-c\sqrt{\log x})$ is computable; no hypothetical zero stands in the way of writing it down. I call $c$ the *clean constant*. It is what the framework inherits from the geometry of long division: an error rate on the cancellation of the collision invariant, honest all the way down, for every base at once.

## L-values in the table

Forty integers sitting in a grid. Read one way, it is a lookup table; give it a prime, it returns a signed integer. That is the surface of the object.

Read another way, the grid is a signal. And signals can be decomposed into frequencies.

For those who have not met it before, the Fourier transform is an instrument for taking something apart into simpler pieces.

Here is something your brain does without being asked. A piano chord reaches your ear as one sound, a single wave of air pressure rising and falling. But you do not hear it as one sound. You hear notes. You can tell which notes are in there. A C, an E, a G. The air carried a mixture. Your ear took the mixture apart.

The Fourier transform is the mathematical tool for doing the same thing. Give it a mixed signal and it hands back the simple pieces the signal is built from, along with a number for how much of each piece is in the mix. The mixture and the list of pieces are two descriptions of the same sound. The mixture is easier to receive, because that is how sound actually arrives; as pressure changing over time. The list of pieces is easier to understand, because once you know the notes, you know what chord you are hearing, you can name it, transpose it, write it down. A pressure curve tells you nothing you can act on. A list of notes tells you everything.

The collision periodic table is not a sound, but it is a signal in the same sense. It assigns a signed integer to each of 40 residue classes. It has a shape, and the shape can be taken apart.

The Fourier transform does the taking-apart. Recall the table lives modulo 100, because the collision invariant depends only on the last two digits of the prime. For a table that lives modulo 100, the "notes" are the Dirichlet characters modulo 100. Each character assigns a number to each class, and each is a frequency of its own, a specific way of oscillating across the 40 cells. The transform asks a simple question. How much of each frequency does my table contain? The answer is a list of coefficients, one per character. Call them Fourier coefficients, or call them the notes the table is playing; it does not matter what you call them.

Now the decomposition theorem from the [previous paper](https://arxiv.org/abs/2604.00054) says each coefficient factors into two pieces; an L-function value at $s = 1$, and a geometric weight that depends only on the base. So when you read the table in the frequency domain, you are reading L-function values.

This is not an analogy. It is an equation. Take the eight primitive odd characters modulo 100. For each one, compute the Fourier coefficient from the table. Divide by the corresponding Bernoulli number and the corresponding L-value at $s=1$:

```
   k    |c_hat|    |B_1|    |L(1)|   ratio
   2     0.462    4.298    1.350    0.0796
   4     0.362    3.804    1.195    0.0796
   6     0.238    3.087    0.970    0.0796
   8     0.138    2.351    0.739    0.0796
```

The ratio is $1/(4\pi) = 0.0796...$. Not one of the eight. All eight. The same irrational constant, involving $\pi$, extracted from a table of forty integers that came out of long division.

The specific value $1/(4\pi)$ is base 10's. Other bases give other closed forms, depending on Euler's totient of the base; that dependence is proved for a few bases and open in general.

The table and the L-values are one object. Turn your head one way, and you see a grid of integers from long division. Turn it the other, and you see the values of an analytic function that governs how primes distribute. The decomposition theorem is the turn of the head.

## The variance

Whichever way you turn, the signal has weight.

The cancellation theorem, the central result of this paper, says the signed collision deviations sum to zero across the primes. But a signed sum reaching zero does not take its ingredients down with it. Fifty primes at $+5$ and fifty at $-5$ sum to zero; the hundred values are still $\pm 5$. The sum measures balance, not size.

So ask a different question. How big are the deviations, on average? Square each one to remove the sign, add the squares across all primes up to $x$, and the total grows linearly with the count. I call this the *variance theorem*:

<div>
$$\sum_{p \le x} |S_{\text{centered}}(p)|^2 \sim \sigma^2(b) \cdot \frac{x}{\log x}$$
</div>

The constant $\sigma^2(b)$ is the *collision variance* at base $b$. In base 10 it works out to about 7.26, and its square root is about 2.7. That number is the typical amplitude of a centered collision value. Every prime, on average, deviates by $\pm 2.7$ from the expected collision count for its class; some more, some less. The amplitude does not shrink as primes get larger. It holds its size forever.

One way to picture it. Each prime takes a single step, left or right, by an amount determined by its last two digits. The cancellation theorem says the crowd's center of mass stays near zero. The variance theorem says the individual steps themselves never shrink. The signal cancels in the aggregate but never goes quiet. Every prime still carries its mark.

## The table

Step back. What you see is a finite grid. Forty integers in base 10, six in base 3, forty-two in base 7. Every prime larger than $b^2$ has a home in this grid, and every prime with the same last two digits shares that home. The prime 1009 and the prime 10009 carry the same signed integer, the same collision fingerprint, and so does every prime ending in 09, at any size, forever. It's proved.

The grid is antisymmetric; its mean is $-1/2$; its Fourier transform encodes L-function special values; its sum across primes cancels at the rate of the prime number theorem. None of this is imposed on the table. Each property falls out of the digit function.

A periodic table of the primes, built from long division.

## Generate it yourself

The table above is base 10. You can generate the collision periodic table at any base:

```
$ ./nfield table --base 3

Collision periodic table, base 3 (mod 9)

       0   1   2
 0:    .  +0  +1
 1:    .  +0  -1
 2:    .  -2  -1

Mean = -1/2. Complement pairs: S(a) + S(9 - a) = -1.
```

Six entries in base 3. Forty-two in base 7. Forty-eight in base 12. The antisymmetry, the $-1/2$ mean, and the Fourier-encoded L-values hold at every base.

Try a few. Pair up complement classes and check they sum to $-1$ by hand. Or let the computer do it:

```
$ ./nfield verify finite-det        # S depends only on p mod b^2
$ ./nfield verify antisymmetry      # S(a) + S(b^2 - a) = -1
$ ./nfield verify decomposition     # Parseval moment identity
```

The theorems are finite, deterministic, and checkable. Every one passes at every base.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Collision Periodic Table](https://github.com/alexspetty/nfield/blob/main/research/collision_periodic_table.pdf)

*Alexander S. Petty*
April 2026
.:.

