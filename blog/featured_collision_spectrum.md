# The Collision Spectrum

Here is a sentence I would not have believed five years ago. Take the [collision periodic table](https://alexpetty.com/the-collision-periodic-table/) in base 10. Forty integers, computed from long division. Square each one, add the squares up, multiply by a constant involving $\pi$. The number that comes out is a weighted sum of L-function values, exactly.

Forty integers from long division on one side. L-function values from the analytic theory of primes on the other. The two have nothing visible to do with each other. They are equal anyway.

That equality is the main result of this paper, and the rest of these notes will sharpen the picture around it. At base 5, the same identity becomes a *fourth* moment of L-function values, written exactly as a sum of squared integers from a finite table. And inside the Fourier coefficients themselves, when the character is quadratic, sit the class numbers of imaginary quadratic fields.

None of this should be possible. Long division should not reach this far. It does anyway.

## From table to spectrum

The collision invariant is the signed integer attached to every prime by long division. [The collision invariant](https://alexpetty.com/the-collision-invariant/) and [the collision periodic table](https://alexpetty.com/the-collision-periodic-table/) walk through where it comes from and why it depends only on the prime's last two digits in any base. In base $b$, the invariants arrange themselves into a finite table modulo $b^2$. In base 10, the table has forty entries.

A finite table is a signal. Signals can be decomposed into frequencies. The natural frequencies for a table modulo $b^2$ are Dirichlet characters, and the decomposition is a Fourier transform. [The collision transform](https://alexpetty.com/the-collision-transform/) proved an antisymmetry theorem that silenced the even half of the spectrum. What remains is the odd half. Each odd character carries one Fourier coefficient, a number that says how loudly the table plays that frequency.

This paper opens those coefficients and looks inside.

## Two pieces in every coefficient

Each coefficient comes apart, exactly, into two pieces. The two pieces have no business being together.

**The first piece knows about primes.** It is a generalized Bernoulli number, written $B_{1,\overline{\chi}}$. The name sounds technical but the object is finite and hand-computable; you can write one down on paper. The reason it matters here is a classical identity Dirichlet discovered in 1837. There is an analytic object called an L-function, an infinite series built from a Dirichlet character. At the value $s = 1$ that series reaches a special number, $L(1, \chi)$, which controls how primes distribute across residue classes. Dirichlet's identity says the generalized Bernoulli number is the same size as $L(1, \chi)$, up to a factor of $b/\pi$:

<div>
$$|B_{1,\overline{\chi}}| = \frac{b}{\pi}\,|L(1,\chi)|$$
</div>

The Bernoulli number is the finite, computable stand-in for the analytic special value. So the first piece of the factorization is, in effect, an L-value at $s = 1$. It is a quantity that knows the primes.

**The second piece knows about digits.** In base 10, look at the residues 00, 11, 22, ..., 99 modulo 100. These are the residues whose two base-10 digits are equal. I call this the *diagonal set*. The second piece, written $S_G(\chi)$, is a sum over the diagonal set: at each $n$ in the set it records the small jump $\overline{\chi}(n+1) - \overline{\chi}(n)$. It encodes the bin geometry of the digit function, and it depends only on the base, not on any prime.

A separate lemma in the paper, the *diagonal reduction*, simplifies $S_G(\chi)$ to twice a short partial character sum:

<div>
$$|S_G(\chi)| = 2\,\Bigl|\sum_{k=1}^{b-1} \overline{\chi}(k)\Bigr|$$
</div>

The right-hand side is the most classical object in the subject of character sums. The diagonal reduction says the collision invariant's bin geometry is the same thing, in disguise.

One piece from the analytic theory of primes. One piece from the bin geometry of long division. Nobody had put them together before. I proved that their product is the Fourier coefficient:

<div>
$$\hat{S}(\chi) = -\frac{B_{1,\overline{\chi}} \cdot \overline{S_G(\chi)}}{\phi(b^2)}$$
</div>

I call this the *decomposition theorem*. The Bernoulli numbers are classical. The diagonal sums are new. The factorization itself, the fact that these two unrelated quantities multiply to give the collision spectrum, is the main result of this paper.

The proof assembles three known ingredients in a new way. A formula for the collision invariant in terms of floor-function slices. The classical Bernoulli identity for character sums over fractional parts. The vanishing of primitive character sums over cosets. Each ingredient is in the literature. Their combination was not.

## Base 5: a sharper version of the surprise

Base 10 is convenient because it has 40 entries and $\pi$ comes out clean. Base 5 is where the identity becomes the most striking.

At base 5, the diagonal reduction has an unexpected payoff: the partial character sum on the right-hand side is *itself* proportional to a Bernoulli number, with the proportionality constant $\sqrt{5}/2$. Working it through:

<div>
$$|S_G(\chi)| = \frac{5\sqrt{5}}{\pi}\,|L(1,\chi)|$$
</div>

Now plug both pieces of the factorization back in. The first piece, $|B_{1,\overline{\chi}}|$, is proportional to $|L(1,\chi)|$. The second piece, $|S_G(\chi)|$, is *also* proportional to $|L(1,\chi)|$. Their product is therefore proportional to $|L(1,\chi)|^2$:

<div>
$$|\hat{S}(\chi)| \propto |L(1,\chi)|^2 \quad (\text{at base } 5)$$
</div>

At base 5, the eight Fourier coefficients of the collision invariant are not just *related* to L-function values. They are squared L-function values, up to a single scaling constant that depends on the base alone.

Consequence. When Parseval takes those Fourier coefficients, squares them, and adds them up, it produces a *fourth* moment of L-function values:

<div>
$$\sum_\chi |L(1,\chi)|^4 = c_5 \sum_a |S(a)|^2$$
</div>

On the left: the fourth moment of an L-function family, an object the analytic theory has been measuring for decades by deep methods. On the right: an integer arithmetic computation that finishes before lunch on a small piece of paper. Six classes modulo 25, eight characters, one constant. The fourth moment of L-function values at $s = 1$ falls out, exactly, from a finite table built by long division.

I would not have believed this either. Then I checked it.

## The class numbers

Inside some of those Fourier coefficients, when you peel them open, sit numbers that have been studied since Gauss.

For a quadratic odd primitive Dirichlet character $\chi_D$ with imaginary discriminant $D < -4$, there is a classical identity:

<div>
$$|L(1,\chi_D)| = \frac{\pi\,h(D)}{\sqrt{|D|}}$$
</div>

The number $h(D)$ is the *class number* of the imaginary quadratic field $\mathbb{Q}(\sqrt{D})$. Class numbers are finicky integers that measure how badly unique factorization fails inside that field. Gauss tabulated them in the 1800s. Their behavior is famously irregular and famously deep.

When the modulus $b^2$ admits primitive odd quadratic characters, the decomposition theorem rewrites the corresponding collision Fourier coefficients in terms of class numbers. Long division at base $b$, applied to a particular residue class, computes a quantity proportional to $h(D)/\sqrt{|D|}$. The same class numbers Gauss compiled by hand emerge from the bin geometry of digit arithmetic.

Once you see this, it is hard to keep treating long division as the elementary topic the textbooks present it as.

## The moment identity

The base-5 result is one face of a more general identity, and the general identity is worth seeing in its own right.

There is a conservation law in Fourier analysis. If you measure the total energy of a signal by squaring its values and adding them up, you get the same answer whether you measure in the original domain or in the frequency domain. This is Parseval's theorem. Physicists use it every day. It is not deep. It is bookkeeping.

But watch what happens when bookkeeping is applied here.

On one side of Parseval: the collision invariant. Forty integers in base 10. Square them, add them up. You can do this with a pencil.

On the other side: the Fourier coefficients. The decomposition theorem has just spelled out what those coefficients are made of. Each one carries an L-function value as a factor. So when Parseval squares the coefficients and adds them up, it assembles a weighted sum of squared L-values:

<div>
$$\sum_{\chi} |L(1,\chi)|^2 \cdot |S_G(\chi)|^2 = \frac{\pi^2 \phi(b^2)}{b^2}\,\sum_{a} |S(a)|^2$$
</div>

The left side involves L-functions, the objects that govern how primes distribute. The right side is a sum of squared integers from a finite table. They are equal. Not in the limit. Not approximately. Equal.

In base 3 you can verify it by hand. Six coprime classes modulo 9. Each carries a small collision value: $0, 1, 0, -1, -2, -1$ (the entries are $0, +1, +0, -1, -2, -1$ across the table). Square them, add them up, multiply by the constant. The number you get is a weighted second moment of L-function values, computed exactly, from integer data.

No complex analysis enters the calculation. No contour integral. No analytic continuation. The $\pi$ on the right side is the $\pi$ Dirichlet put into the Bernoulli identity in 1837. Long division produces a number that the analytic theory of primes also produces. Two roads. One number.

I did not expect this. The collision invariant counts how remainders fall into bins during long division. Nothing in its definition suggests it should know the values of L-functions. But the decomposition theorem plants an L-value inside each Fourier coefficient, and Parseval collects them into a moment identity. The digit function, without knowing it, computes something about the distribution of primes.

## The bridge

Number theory has two countries.

One is discrete: integers, divisibility, finite tables, things you can count on your fingers. The other is continuous: functions of a complex variable, infinite series, zeros drifting in the critical strip. The great results in the subject are bridges between them. Euler built the first one in 1737, when he showed the prime counting function is governed by the Riemann zeta function. Dirichlet built another in 1837, when he proved primes in arithmetic progressions are controlled by L-functions. Each bridge takes something you can count and connects it to something you can analyze.

This paper builds a bridge of the same kind, in miniature.

On one side: the collision invariant. A finite table of signed integers, one per residue class, computable from long division. On the other side: L-function special values at $s = 1$, the analytic machinery that controls the primes, and through them the class numbers Gauss tabulated by hand. The decomposition theorem says these are the same information. Not approximately. Not in the limit. The collision weight at each frequency is the product of an L-value and a geometric factor, and the factorization is exact. The finite table and the L-function landscape are two descriptions of a single object, written in different languages. The decomposition theorem is the dictionary.

There is a small extra observation worth making. An L-function does its main work along the critical strip, far from $s = 1$. The collision invariant only knows about $s = 1$, the boundary. So how can the boundary value say anything about the strip? The paper makes the connection explicit. The Fourier expansion of the centered collision sum is an exact identity in which each character's contribution is multiplied by a coefficient proportional to $L(1, \chi)$ through the Bernoulli number $B_1(\bar\chi)$. When $L(s, \chi)$ has a zero deep in the strip, $\log L(s, \chi)$ blows up at that zero, and the size of the resulting contribution is bounded in terms of $L(1, \chi)$. The behavior at the edge bounds the behavior at depth. The collision invariant lives on the edge, but the edge is not isolated.

## Where the bridge begins

Every bridge in number theory starts somewhere specific. Euler started with $\sum 1/p$. Dirichlet started with character sums. This one starts with $\lfloor br/p \rfloor$. A floor function. The single step of long division that turns a remainder into the next digit. It should not reach this far into the theory of primes. It does anyway.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Preprint: [The Collision Spectrum](https://arxiv.org/abs/2604.00054)

*Alexander S. Petty*
March 2026
.:.
