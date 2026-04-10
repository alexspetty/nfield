# The Collision Periodic Table

In 1869, Mendeleev arranged the known elements into a grid. Each element had a weight, a valence, a set of chemical properties. The grid organized them. Gaps in the grid predicted elements that had not yet been found. The periodic table turned chemistry from a catalog into a science.

The collision invariant does something similar for primes.

Here is the surprise. Take any prime larger than 100, say 1234567891. Look at its last two digits: 91. There is a number attached to that prime, a single signed integer, and this number is determined entirely by 91. Not by the rest of the prime. The 1234567 in front does not enter. Every prime ending in 91 carries the same number. The prime 191 carries it, the prime 1091 carries it, the prime $10^{100} + 91$ carries it. They share a fingerprint, and the fingerprint comes from the last two digits.

The number is called the collision invariant. It comes out of long division: the digit function $\lfloor br/p \rfloor$ distributes the remainders of $p$ into bins, and the collision invariant counts how the bins fill. The first three papers ([A](https://arxiv.org/abs/2604.00045), [B](https://arxiv.org/abs/2604.00047), [C](https://arxiv.org/abs/2604.00054)) in this series proved that this count depends on nothing but the prime's last two digits. Not approximately. Exactly. Forever.

So there is a table. Every base has one. Base 3 has 6 entries. Base 7 has 42. I work in base 10 because it is familiar, but the structure is not about base 10. The base is a lens. Different lenses give different tables, but they are all looking at the same thing; the arithmetic of the primes, which does not depend on how those primes are written down.

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

Row is the tens digit, column is the units digit. Dots mark classes that share a factor with 100, and primes never land there. Every prime larger than 100 maps to exactly one cell. The prime 109 lands at row 0, column 9, and carries +8. The prime 1091 lands at row 9, column 1, and carries $-9$. The prime 10007 lands at row 0, column 7, and carries 0. A table lookup replaces a computation.

Look at the grid for a moment. It does not look random. It is antisymmetric: the entry at 09 is $+8$, the entry at 91 is $-9$. Their sum is $-1$. Try another pair. The entry at 03 is $+2$, the entry at 97 is $-3$. Their sum is $-1$. Every complement pair, without exception, sums to $-1$. The mean across the whole table is $-1/2$. Not approximately. The number $-1/2$, exactly. Almost nothing in nature lands on a clean rational number like that. Forty integers from a digit-counting procedure should not have an arithmetic mean of $-1/2$, and yet they do, and the reason runs through the same symmetry that organizes everything else in this corner of mathematics.

## The cancellation

The entries in the table run from $-9$ to $+8$. Some cells are positive. Some are negative. Zero is a common value; $+8$ and $-9$ are the extremes.

Now imagine the primes arriving in order, one after another, each one landing in exactly one cell. The prime 109 arrives, hands over $+8$, and steps aside. The prime 113 arrives, hands over $-1$, and steps aside. The prime 127 hands over $+1$. The prime 131 hands over $-1$. An endless stream of primes, each handing over a signed integer as it passes.

Keep a running total. Does it climb? Does it fall? Does it balance?

This is the kind of question the classical prime theory was built to answer. Primes are evenly spread across the cells in the long run; each class gets its fair share. So whether the running total stays small depends on whether the positive entries and the negative entries cancel out when each cell is visited equally often. The whole table averages to $-1/2$, not zero. So the running total does not aim at zero; it aims at the line that runs through $-1/2$ per prime. Subtract that line off, and you have a centered count that *does* aim at zero. The question becomes a clean one. Does the centered count actually hit zero, or does it drift?

It cancels. At the prime number theorem rate:

<div>
$$\sum_{p \le x} S_{\text{centered}}(p) = O\!\left(x \exp(-c\sqrt{\log x})\right)$$
</div>

The positive fluctuations and the negative fluctuations destroy each other. The main term is zero. The collision invariant, a quantity built from long division, cancels across primes at the same rate that the prime counting function approaches the logarithmic integral.

My proof uses no new analytic machinery. It cannot; the analytic theory of prime distribution is over a century old and thoroughly worked. The bridge between the collision invariant and that classical machinery is a [decomposition theorem](https://arxiv.org/abs/2604.00054) I built in the previous paper. It writes the centered collision value as a clean combination of objects the textbooks already know how to handle, the kind of objects whose cancellation across primes is settled. Once the rewrite is done, the classical machinery picks the proof up and carries it the rest of the way.

## The clean constant

There is an asterisk attached to the classical prime number theorem for arithmetic progressions, and it has lived there for a century.

The asterisk is a hypothetical zero. Nobody has ever found one. Nobody has ever proved they cannot exist. The story goes like this. Choose a way to slice the primes by residue class, and the classical theory tells you each class gets its fair share. The theory also gives you an error term, a number that controls how fast the share converges. For most ways of slicing, the error term has a clean constant in it, a number you can compute and write down. But for a few specific slicings, the constant becomes *ineffective*. You can prove the primes balance, but you cannot say how fast, because the speed depends on a hypothetical object called a Siegel zero, an object nobody has ever produced and nobody has ever ruled out.

A century of work has not removed this asterisk. It is one of the hardest obstructions in analytic number theory.

The collision periodic table has no asterisk. Its slicing is the slicing by last two digits, which happens to have a perfect-square modulus, $b^2$. For any base $b \geq 3$, the perfect-square shape eliminates the kind of exceptional behavior a Siegel zero would require. The obstruction vanishes, not because of a hard new argument, but because the modulus is the wrong shape for it to exist.

I did not engineer the modulus to avoid Siegel zeros. I was not thinking about Siegel zeros at all. The modulus $b^2$ emerged from the digit function; the collision invariant depends on two base-$b$ digits, so it lives modulo $b^2$. It happens that this is exactly the shape of modulus the century-old obstruction cannot reach.

This is the deeper thing the result does. It takes a prime-distribution question the classical framework can state but cannot always bound with a written-down constant, and it gives an effective bound, unconditionally, for every base. The constant $c$ in the error term $x\exp(-c\sqrt{\log x})$ is computable. No hypothetical zero blocks the way. I call $c$ the *clean constant*. It is what the framework inherits from the geometry of long division: an error rate on the cancellation of the collision invariant, honest all the way down, for every base at once.

## L-values in the table

Forty integers sitting in a grid. Read one way, the grid is a lookup table: hand it a prime, it hands back a signed integer. That is the surface of the object.

Read another way, the grid is a signal. And signals can be decomposed.

If you have not met it before, the Fourier transform is an instrument for taking things apart into simpler pieces. Here is something your brain does without being asked. A piano chord reaches your ear as one sound, a single wave of air pressure rising and falling. But you do not hear it as one sound. You hear notes. You can tell which notes are in there. A C, an E, a G. The air carried a mixture. Your ear took the mixture apart.

The Fourier transform is mathematics' version of the same operation. Give it a mixed signal and it hands back the simple pieces the signal is built from, along with a number for how much of each piece is in the mix. The mixture and the list of pieces are two descriptions of the same sound. The mixture is easier to receive, because that is how sound actually arrives, as pressure changing over time. The list of pieces is easier to understand, because once you know the notes, you can name the chord, transpose it, write it down. A pressure curve tells you nothing you can act on. A list of notes tells you everything.

The collision periodic table is not a sound, but it is a signal in the same sense. It assigns a signed integer to each of 40 residue classes. It has a shape, and the shape can be taken apart.

So I asked the Fourier transform to take it apart. The "notes" available to a table that lives modulo 100 are a specific finite set, one note for each way of cleanly oscillating across the 40 cells. The transform asks a single question of each note: how much of you is in this table? The answer is a number, one per note. Call them Fourier coefficients, or call them the notes the table is playing; it does not matter what you call them.

Here is where the surprise lives. The decomposition theorem from the [previous paper](https://arxiv.org/abs/2604.00054) says each of those coefficients factors. It comes apart into two pieces. One piece is a value of an L-function, an object from the deep analytic theory of primes. The other piece is a geometric weight that depends only on the base. So when you read the table in the frequency domain, **you are reading L-function values**. The grid built from long division is a list of L-values in disguise.

This is not an analogy. It is an equation. To check it, take the eight notes that carry the content (they pair up by complex conjugation, four magnitudes covering all eight). For each one, read the Fourier coefficient off the table, then divide by two textbook quantities, a Bernoulli number and an L-value at $s = 1$:

```
   k    |c_hat|    |B_1|    |L(1)|   ratio
   2     0.462    4.298    1.350    0.0796
   4     0.362    3.804    1.195    0.0796
   6     0.238    3.087    0.970    0.0796
   8     0.138    2.351    0.739    0.0796
```

Look at the right column. Four different Fourier coefficients, four different Bernoulli numbers, four different L-values, four different ratios. They all come out to the same number. They all come out to $0.0796\ldots$, which is $1/(4\pi)$. Not one of the four. All four, and by conjugation all eight. The same irrational constant, with $\pi$ inside it, falls out of a table of forty integers that came out of long division.

The specific value $1/(4\pi)$ is base 10's. Other bases give other closed forms, depending on Euler's totient of the base. That dependence is proved for a few bases and open in general.

The table and the L-values are one object. Turn your head one way, and you see a grid of integers from long division. Turn it the other, and you see the values of an analytic function that governs how primes distribute. The decomposition theorem is the turn of the head.

## The variance

Whichever way you turn, the signal has weight.

The cancellation theorem says the signed collision deviations sum to zero across the primes. But a signed sum reaching zero does not take its ingredients down with it. Fifty primes at $+5$ and fifty at $-5$ sum to zero; the hundred values are still $\pm 5$. The sum measures balance, not size.

So ask a different question. How big are the deviations, individually? Square each one to remove the sign, add the squares across all primes up to $x$, and the total grows linearly with the prime count. I call this the *variance theorem*:

<div>
$$\sum_{p \le x} |S_{\text{centered}}(p)|^2 \sim \sigma^2(b) \cdot \frac{x}{\log x}$$
</div>

The constant $\sigma^2(b)$ is the *collision variance* at base $b$. In base 10 it works out to about 7.26, and its square root is about 2.7. That number is the typical amplitude of a centered collision value. Every prime, on average, deviates by $\pm 2.7$ from the line that runs through its class. Some more, some less. The amplitude does not shrink as primes get larger. It holds its size forever.

One way to picture it. Each prime takes a single step on a number line, left or right, by an amount determined by its last two digits. The cancellation theorem says the crowd's center of mass stays close to zero, no matter how large the crowd grows. The variance theorem says each individual step is still a real step. The signal cancels in the aggregate but never goes quiet. Every prime still carries its mark.

## The whole grid

Step back. What you see is a finite grid. Forty integers in base 10, six in base 3, forty-two in base 7. Every prime larger than $b^2$ has a home in this grid, and every prime with the same last two digits shares that home. The prime 1009 and the prime 10009 carry the same signed integer, the same collision fingerprint, and so does every prime ending in 09, at any size, forever. It's proved.

The grid is antisymmetric; its mean is $-1/2$; its Fourier transform encodes L-function special values; its sum across primes cancels at the rate of the prime number theorem; the typical step it carries holds its size forever. None of this is imposed on the table. Each property falls out of the digit function.

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

