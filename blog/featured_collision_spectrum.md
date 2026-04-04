# The Collision Spectrum

The [previous paper](https://arxiv.org/abs/2604.00047) decomposed the collision invariant into its natural frequencies: Dirichlet characters. The antisymmetry theorem silenced the even half. What remained were the odd characters, each carrying a Fourier coefficient.

A coefficient is a number. It tells you how loud that frequency is. This paper opens those coefficients and looks inside. What I found is the center of this research program.

## The factorization

Each coefficient factors. Exactly. Into two pieces that have no business being together.

The first piece knows about primes. It is a generalized Bernoulli number $B_{1,\overline{\chi}}$, a finite sum that has been studied since the 19th century. What makes it relevant here is a classical identity: the size of this Bernoulli number equals the size of an L-function at $s = 1$, up to a known constant. An L-function is an infinite series, built from a Dirichlet character, that encodes information about primes. At $s = 1$ it reaches a special value that controls how primes distribute across arithmetic progressions. Dirichlet discovered this in 1837. The Bernoulli number is a finite, computable stand-in for the same information.

The second piece knows about digits. It is a finite-difference sum $S_G(\chi)$ anchored at a specific set of residue classes. The anchor set consists of the classes whose two base-$b$ digits are equal; in base 10, these are 00, 11, 22, ..., 99 modulo 100. I call this the *diagonal set*. The sum $S_G$ records the jumps in $\overline{\chi}$ as you step past each diagonal class, $\overline{\chi}(n+1) - \overline{\chi}(n)$ for each $n$ in the set. It encodes the bin geometry of the digit function, and it depends only on the base, not on any prime.

One piece from number theory. One piece from the geometry of long division. Nobody had put them together before. I proved that their product is the Fourier coefficient:

$$\hat{S}(\chi) = -\frac{B_{1,\overline{\chi}} \cdot \overline{S_G(\chi)}}{\phi(b^2)}$$

I call this the *decomposition theorem*. The Bernoulli numbers are classical. The diagonal sums are new. The factorization itself, the fact that these two quantities multiply to give the collision spectrum, is the main result of this paper.

The proof assembles three known ingredients in a new way: a formula for the collision invariant in terms of floor-function slices, the Bernoulli identity for character sums over fractional parts, and the vanishing of primitive character sums over cosets.

## The moment identity

There is a conservation law in Fourier analysis. If you measure the total energy of a signal by squaring its values and adding them up, you get the same answer whether you measure in the original domain or in the frequency domain. This is Parseval's theorem. Physicists use it every day. It is not deep. It is bookkeeping.

But watch what happens when you apply it here.

On one side of Parseval: the collision invariant. Forty integers in base 10. Square them, add them up. You can do this with pencil and paper.

On the other side: the Fourier coefficients. But the decomposition theorem just told us what those coefficients are made of. Each one carries an L-function value as a factor. So when Parseval squares them and adds them up, it assembles a weighted sum of squared L-values:

<div>
$$\sum_{\chi} |L(1, \chi)|^2 \cdot |S_G(\chi)|^2 = \frac{\pi^2 \phi(b^2)}{b^2} \sum_{a} |S(a)|^2$$
</div>

The left side involves L-functions, the objects that govern how primes distribute. The right side is a sum of squared integers from a finite table. They are equal.

In base 3 you can check this by hand. There are 6 coprime classes modulo 9, each carrying a collision value. Square them, add them up, multiply by the constant. You get a weighted second moment of L-function values, computed exactly, from integer data.

No complex analysis entered the computation. The $\pi$ comes from the Bernoulli identity, not from analytic continuation.

I did not expect this. The collision invariant counts how many remainders land in the same bin during long division. There is no reason, from its definition, to expect it to know the values of L-functions. But the decomposition theorem plants an L-value inside each Fourier coefficient, and Parseval collects them into a moment identity. The digit function, without knowing it, computes something about the distribution of primes.

## The bridge

Number theory has two countries. One is discrete: integers, divisibility, finite tables, things you can count. The other is continuous: functions of a complex variable, infinite series, zeros drifting in the critical strip. The great results in the subject are bridges between them. Euler built one in 1737 when he showed the prime counting function is governed by the zeta function. Dirichlet built another in 1837 when he proved primes in arithmetic progressions are controlled by L-functions. Each bridge connects something you can count to something you can analyze.

This paper builds a small bridge of the same kind.

On one side: the collision invariant. A finite table of signed integers, one per residue class, computable from long division. On the other: L-function special values at $s = 1$, the analytic machinery that controls the primes.

The decomposition theorem says these are the same information. Not approximately. Not in the limit. The collision weight at each frequency is the product of an L-value and a geometric factor, and the factorization is exact. The finite table and the L-function landscape are two descriptions of a single object, written in different languages.

Every bridge in number theory starts somewhere specific. Euler started with $\sum 1/p$. Dirichlet started with character sums. This one starts with $\lfloor br/p \rfloor$. A floor function. The operation a child performs when doing long division. It should not reach this far into the theory of primes. But here we are.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Collision Spectrum](https://arxiv.org/abs/2604.00054)

*Alexander S. Petty*
March 2026
.:.

