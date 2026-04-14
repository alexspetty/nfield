# The Character Structure of the Collision Fluctuation

$\log \log x$. Take any number $x$. Compute its logarithm. Then compute the logarithm of *that*. The result is what mathematicians write as $\log \log x$, and it is one of the slowest-growing functions you can write down without it being constant. Between a million and a trillion (a factor of a million in $x$), $\log \log x$ increases by less than one. Between a trillion and a quadrillion, by less than half. To make $\log \log x$ grow by ten, you need $x$ to roughly double its number of digits twenty times in a row. It is so sluggish that you can walk through truly enormous stretches of primes and not see it move at all.

That is how fast a particular sum across primes grows. The sum is the *collision fluctuation*, weighted by $1/p$ and taken over all primes up to a cutoff $x$ in a fixed base. Each prime contributes a small signed integer, the *fluctuation*, which I will call $\Delta_p$ when I need a name for it. The fluctuation is the difference between the prime's collision count (the count whose structure [bin derangements](https://alexpetty.com/bin-derangements-and-the-gate-width-theorem/) worked out via the gate width theorem) and the average collision count over all the constructive multipliers at that prime. Some primes contribute fluctuations above the local average. Some below. The signs jump around with no obvious pattern. But the partial sums drift slowly downward, on a curve that looks more and more like $-\mu \cdot \log \log x$ as $x$ grows. The constant $\mu$ depends on the base and is around $0.68$ in base ten.

So we have a sum across primes that grows at the slowest interesting rate in analysis. That curve encodes something, and this paper takes the growth and splits it into pieces, character by character, and asks what each piece carries. The splitting itself is proved. What comes out the other side is mostly conjecture supported by numerical evidence.

## Splitting the signal

In base $10$, every prime past $5$ ends in one of four digits. $1$, $3$, $7$, or $9$. Each one is a *residue class modulo $10$*, which is just a fancy way of saying "the set of all numbers that share the same last digit in base ten". The primes ending in $1$ form their own subsequence inside the primes. So do the primes ending in $3$, in $7$, in $9$. Four parallel streams of primes, sorted by last digit.

The natural question, given that we want to split a sum across primes, is whether the four streams contribute differently to the total. Maybe primes ending in $1$ do most of the work and primes ending in $9$ barely matter. Or maybe the four streams contribute equally and the total is just four copies of the same thing. Or maybe the truth is somewhere in between, with each stream carrying its own characteristic signal.

The tool for sorting this out has been around since $1837$, when Dirichlet invented it to prove that every residue class has infinitely many primes. The tool is called a *Dirichlet character*. The name is heavy, but the idea is light.

A Dirichlet character is a recipe for assigning a small complex number to each residue class, with one rule. The number assigned to a product of two classes has to equal the product of the numbers assigned to each. So if a character assigns the value $i$ (the imaginary unit) to the class of primes ending in $3$, and the value $-1$ to the class ending in $7$, then it must assign $-i$ to the class ending in $1$, because $3 \times 7 = 21$ ends in $1$ and the values have to multiply correctly. The character *respects multiplication*, in that sense. It is a way of weighting the four classes that plays nicely with how the classes combine.

How many such recipes exist in base ten? Exactly four. The count is given by a number-theoretic function called *Euler's totient*, written $\varphi(b)$, which counts the residues mod $b$ that are coprime to $b$. In base ten the coprime residues are $\{1, 3, 7, 9\}$, so $\varphi(10) = 4$, and the number of Dirichlet characters mod $10$ is also four. One of the four characters is the *trivial* character, which assigns the value $1$ to every class. The other three are non-trivial, assigning different complex weights to the four classes in ways that respect multiplication.

These four characters do for the residues coprime to $10$ what sines and cosines do for periodic signals on the real line. They form an *orthogonal basis*, which means any function defined on the four classes can be uniquely expanded as a weighted sum of the four characters. The trivial character carries the average of the function across all four classes. The non-trivial characters carry the corrections, the part that says how much each class deviates from the average.

Apply this to the collision fluctuation. For each character $\chi$ mod $b$, take the fluctuation $\Delta_p$ at each prime $p$, multiply it by $\chi(p)$ (the character's complex weight on that prime's residue class), divide by $p^s$ (a damping factor that makes large primes count less, with the *exponent* $s$ as a knob we get to vary), and add up over all primes past the base:

$$L_\chi(s, \ell) = \sum_{p > b} \frac{\chi(p) \cdot \Delta_p(\ell)}{p^s}.$$

Reading the formula left to right. $L_\chi$ on the left is the name we are giving the result. It is a function of two variables, $s$ (the exponent in the denominator) and $\ell$ (the *lag*, the shift distance in the repetend that determines which fluctuation $\Delta_p$ we are measuring). On the right, the symbol $\sum$ means *sum over*, and the subscript $p > b$ says we sum over all primes larger than the base. Inside the sum, we multiply three things at each prime: the character's weight $\chi(p)$, the fluctuation $\Delta_p(\ell)$, and the inverse power $1/p^s$. The result of the whole calculation is a single complex number for each choice of character $\chi$, exponent $s$, and lag $\ell$.

There are four such numbers in base ten, one for each character. Each one is a separate signal, a separate measurement of how the collision fluctuation behaves on the residue classes the character emphasizes. They are the four pieces the original sum splits into.

The proposition that ties everything together is short. **The fluctuation taken only over primes in a single residue class $r$ is a finite linear combination of the four character components**, with weights $\overline{\chi}(r) / \varphi(b)$ where $\overline{\chi}$ is the complex conjugate of $\chi$. This is just the orthogonality of Dirichlet characters applied to the partition of primes by residue class. It is the same identity Dirichlet used in $1837$ to prove there are infinitely many primes in every coprime class. Here it is applied to a different signal, the collision fluctuation, but the algebra is the same. It is the only proved result in this paper, and everything else hangs on it.

## Four components in base ten

Compute the four character components numerically and see what they look like. Here is the table from the underlying research note, base $10$ at lag $\ell = 1$, walking up through primes:

```
$ ./nfield character_components 10 --lag 1

primes ≤ x    |L_χ₀|   |L_χ₁|   |L_χ₂|   |L_χ₃|
----------    ------   ------   ------   ------
   100        1.073    0.254    0.321    0.254
   500        1.278    0.356    0.350    0.356
   800        1.341    0.380    0.355    0.380
  1225        1.393    0.398    0.350    0.398
```

A few words on what the columns mean. Each column is one of the four Dirichlet characters mod $10$. They are conventionally numbered $\chi_0, \chi_1, \chi_2, \chi_3$, with $\chi_0$ always being the trivial character (the one that gives every class the weight $1$) and $\chi_1, \chi_2, \chi_3$ being the three non-trivial characters in some standard order. The vertical bars $|L_{\chi_0}|$ mean *the absolute value*, or *magnitude*, of the complex number $L_{\chi_0}(1, 1)$. Since the character values are complex, the partial sums are complex, and we need a real number to compare. The magnitude is the natural choice.

Reading down the rows, you can see all four magnitudes growing as we add more primes to the sum. The trivial character $\chi_0$ carries the largest weight by some margin, climbing past $1.4$ by the time we have a thousand primes in the sum. The three non-trivial characters carry smaller weights, around $0.35$ to $0.40$ apiece. The characters $\chi_1$ and $\chi_3$ are *complex conjugates* of each other (one is built from $i$ where the other has $-i$), and conjugation preserves magnitudes, so $|L_{\chi_1}| = |L_{\chi_3}|$ exactly. The table confirms this on every row, all the way down.

All four components appear to be growing at the same rate, the same $\log \log x$ creep. The trivial character carries the bulk of the signal because it averages the fluctuation across all classes with equal weight. The non-trivial characters carry the per-class corrections, the part that says how much each residue class deviates from the average. They are smaller in magnitude but they grow at the same rate.

This is one piece of the wonder. The collision fluctuation does not concentrate in one residue class. It spreads across all four, with each class carrying a character-specific weight, and all four weights grow at the same rate at the boundary.

## Not the classical L-values

Look at the magnitudes again and ask the natural question. Are these character components proportional to the classical *Dirichlet $L$-values*?

A quick word on the comparison. For each Dirichlet character $\chi$, classical analytic number theory defines an infinite series called a *Dirichlet $L$-function*,

$$L(s, \chi) = \sum_{n = 1}^{\infty} \frac{\chi(n)}{n^s},$$

which sums the character's values across all positive integers, weighted by $1/n^s$. At the special exponent $s = 1$, this series converges to a specific number, $L(1, \chi)$. These special values $L(1, \chi)$ govern how primes distribute across residue classes — they are the quantities Dirichlet himself studied to prove the prime infinitude theorem in $1837$, and they have been one of the central objects of analytic number theory ever since. So if our new character components $L_\chi(s, \ell)$ are proportional to $L(1, \chi)$ at $s = 1$, that would be the cleanest possible answer. The new objects would be the old objects in disguise.

They appear not to be. In base $10$ at lag $\ell = 1$, the underlying research note computes the ratios

$$\frac{|L_{\chi_2}(1, 1)|}{|L(1, \chi_2)|} \approx 0.54, \qquad \frac{|L_{\chi_1}(1, 1)|}{|L(1, \chi_1)|} \approx 0.40.$$

The numerators are the magnitudes of our character components from the previous section. The denominators are the magnitudes of the classical $L$-values at the same characters. The ratios should be constants if the two are proportional. They are not. They are not simple rational numbers (they do not look like $1/2$ or $2/3$ or anything clean), they depend on the lag $\ell$ (changing $\ell$ moves the ratio), and they change shape from base to base.

So the character components $L_\chi(s, \ell)$ are something new. They live in the same space the classical $L$-functions live in, they are built from the same Dirichlet characters, but they carry information that the classical $L$-functions do not directly encode. This is numerical evidence, not a theorem. But the evidence is consistent across every test, and the conclusion the research note draws is appropriately cautious. The collision fluctuation produces a new family of arithmetic objects, distinct from the classical ones, that the rest of the program is going to need a name for.

## Five bases, the same shape

The growth law is not an artifact of base $10$. Computation in five different bases shows the same qualitative behavior at the same critical boundary:

```
$ ./nfield mertens_growth --bases 3,6,7,10,12 --lag 1

  base    Φ_x(1, 1) at x = 8000   Φ_x(0.9, 1) behavior
  ----    ----------------------   --------------------
    3            -1.38              diverging (power law)
    6            -1.29              diverging (power law)
    7            -1.34              diverging (power law)
   10            -1.37              diverging (power law)
   12            -1.32              diverging (power law)
```

A reading guide for the table. The first column is the base $b$ we are computing in. The second column is the value of the partial sum $\Phi_x(1, 1)$, where $\Phi$ is the *total* fluctuation sum (the trivial-character component, summing the fluctuations over *all* primes coprime to the base). The two arguments inside the parentheses are the exponent $s = 1$ and the lag $\ell = 1$. So $\Phi_x(1, 1)$ is "the total collision fluctuation, weighted by $1/p$, over all primes up to $x$, at lag $1$". The cutoff $x$ is fixed at $8000$ across the table. The third column tries the same sum at a smaller exponent, $s = 0.9$, and reports whether the partial sums look like they are converging to a finite limit or running off to infinity.

Here is what the table says. At $s = 1$, every base gives a partial sum near $-1.3$ to $-1.4$, growing slowly (the $\log \log x$ creep from earlier). At $s = 0.9$, every base diverges, and the divergence is power-law fast rather than logarithmically slow. The critical boundary sits exactly at $s = 1$ in every base tested, which is to say, that is where the convergence falls apart.

The base controls the quantitative details. The Mertens constant $\mu_\ell$ in $\Phi_x(1, \ell) \sim -\mu_\ell \cdot \log \log x$ depends on the base. The per-class biases depend on the base. The exact numbers in the second column depend on the base. But the *qualitative structure* — slow growth at $s = 1$, fast divergence below — does not move. This is the universality conjecture from the underlying research note. It is supported by computation in five bases. It is not proved in any base.

## Flat across the spectrum

The character decomposition is one way to split the fluctuation. There is another, orthogonal to it.

A few terms first. A *primitive root* of a prime $p$ in base $b$ means that the powers of $b$ run through every nonzero residue modulo $p$ before they cycle back to the start. In base $10$, the prime $7$ has $10$ as a primitive root because $10, 100, 1000, \ldots$ modulo $7$ visits every residue $1, 2, 3, 4, 5, 6$ before repeating. Not every prime has this property in every base. In base $10$, only about $37\%$ of primes do. The ones that do are the *primitive root primes*, and their structure is cleaner than the rest.

The *cross-alignment matrix* is a square table of numbers attached to each prime, built from the digit function in a way that the [cross-alignment matrix](https://alexpetty.com/the-cross-alignment-matrix/) paper sets up in detail. For a primitive-root prime, this matrix has a clean diagonalization. Its diagonal entries (its *eigenvalues*, the natural numbers that come out when you turn the matrix into its simplest possible form) carry the spectral content of the prime's digit field. Each eigenvalue is indexed by an integer $k$, called the *frequency*, and runs from $k = 1$ up through $b - 1$.

As the prime grows, each eigenvalue $\lambda_k$ converges to a specific limit determined by the base alone. The difference between $\lambda_k$ at any particular prime and its limit is the *eigenvalue fluctuation* at frequency $k$, written $\psi_p(k)$. Like the collision fluctuation, this is a small signed number that measures how far a prime sits from its asymptotic behavior. We can sum these eigenvalue fluctuations across primes, weighted by $1/p$, exactly the same way:

$$G(s, k) = \sum_{p > b} \frac{\psi_p(k)}{p^s}.$$

Here $G$ is the new sum, $s$ is the same exponent as before, and $k$ is the frequency we are looking at. The natural question is whether each $G(1, k)$ converges (the partial sums settle to a finite limit) and what value it converges to.

The data is striking:

```
$ ./nfield spectral_fluctuation 10 --primes 1000

primes ≤ x   G(1,1)   G(1,2)   G(1,3)   G(1,4)   G(1,5)
----------   ------   ------   ------   ------   ------
   100       0.1642   0.1642   0.1642   0.1640   0.1639
   500       0.1650   0.1650   0.1649   0.1646   0.1644
  1000       0.1651   0.1651   0.1650   0.1646   0.1644
```

Five different frequencies, five different sums, all converging to nearly the same value, around $0.165$. The collision fluctuation distributes its energy *evenly across the spectrum*. No harmonic mode dominates. The chord drifts, but it drifts uniformly at every frequency.

This is the spectral equidistribution conjecture. Computation in base $10$ shows convergence to within a few digits across the first five frequencies. Whether this holds at every frequency, and whether the limiting value has a closed form, are open questions.

## Around the polarity circle

There is a third axis of structure, and it comes from a different kind of observable.

The cumulative polarity of the repetend traces a path on the fixed circle of residues modulo $b - 1$. At each position of the repetend, the running digit sum modulo $b - 1$ takes one of $b - 1$ values. Count how many positions land on each value. The result is the polarity histogram, a vector of $b - 1$ counts that records how the field is distributed around its polarity circle.

For primes where $b$ is a primitive root, the polarity histogram appears to approach the uniform distribution as $p$ grows. The path visits each value approximately $L/(b-1)$ times. The polarity circle is the limiting equilibrium, and the field approaches it.

The collision fluctuations measure departure from this equilibrium. The Mertens growth law asserts that the departures, weighted by $1/p$, accumulate at rate $\log \log x$. The spectral equidistribution asserts that the departures are flat across the harmonic spectrum. Together, the two say the field approaches its equilibrium on the fixed polarity circle, and the rate of approach is controlled by the critical boundary $s = 1$.

This is observational. None of the polarity statements are proved here. They are the third leg of the same structural conjecture, sketched in the underlying research note as a piece of the landscape that needs its own paper to formalize.

## One refraction, three readings

Picture the collision fluctuation as a beam of light entering a prism. The picture is metaphorical. The structure it reveals is not. One beam goes in, one refracted spectrum comes out, and that spectrum can be read three independent ways.

Read it by *Dirichlet character*. Sort the primes by their last digit and the spectrum splits into one clean component per residue class. In base ten, four classes, four components. The split is [proved](https://github.com/alexspetty/nfield/blob/main/research/collision_character_structure.pdf).

Read it by *harmonic frequency*. Sort by which eigenvalue of the cross-alignment matrix the prime is sitting on, and the spectrum spreads its weight evenly across all the eigenvalues. Every frequency carries the same drift. The split is conjecture.

Read it by *polarity*. Sort by where each prime's running digit sum lands on the polarity circle, and the spectrum spreads uniformly around the circle. Every position on the circle gets the same share. The split is observational.

Three readings of the same refracted light. The readings have nothing in common in how they are made. The first one cares about the arithmetic of residues. The second cares about the eigenvalues of a matrix. The third cares about the geometry of digit sums on a circle. They share no machinery, they live in three completely different mathematical spaces, and they produce three answers in three different shapes. They have no business agreeing on anything.

They agree precisely.

Each of the three readings locates the same critical boundary at $s = 1$. The character components grow logarithmically at exactly $s = 1$. The frequency fluctuations converge at exactly $s = 1$. The polarity equidistribution sets in at the rate controlled by exactly $s = 1$. Three completely independent decompositions, three different mathematical machineries, three different shapes of answer. One critical exponent. Hit on the nose by all three.

A noise signal would refract into no structure under any reading. A signal with structure visible to one reading might be a fluke. Two readings, a coincidence. Three independent readings, all locating the same critical boundary in the same refracted spectrum, is not a coincidence. It is an architecture.

The collision fluctuation has an architecture. Every paper that follows is the work of mapping it.

## A note from 2026

*April 2026*

This paper sits at an interesting hinge. Reading it now, four years later, almost every conjecture in the body got upgraded to a theorem at some point in the work that followed.

The character decomposition that I marked as the only proved result here became the central technical move of the entire collision program. By the time of [the collision spectrum](https://alexpetty.com/the-collision-spectrum/), the same orthogonality argument was being applied not to the fluctuation sum but to the collision invariant table itself, and the resulting Fourier coefficients carried L-function values via the decomposition theorem. The "$L_\chi(s, \ell)$ is something new" observation here became the precise statement that the Fourier coefficients of the collision invariant factor as $B_1(\bar\chi) \cdot S_G(\chi) / \varphi(b^2)$, which is the decomposition theorem of the formal preprint. The "new family of arithmetic objects" I was groping toward turned out to be the elementary side of the Bernoulli-L-value formula, and the constant $1/(4\pi)$ that mediates the connection is universal across bases and characters. None of that was visible from this paper alone. It needed three more years of work to come into focus.

The universality conjecture across bases survived and got sharper. The Mertens growth law $\Phi_x(1, \ell) \sim -\mu_\ell \cdot \log \log x$ now has a clean per-class breakdown via the antisymmetry of the collision invariant table, and the constant $\mu_\ell$ has a closed-form expression in terms of the table entries themselves. The "five bases, the same shape" computational evidence from this paper became the first signal that the structure was base-independent at every depth of the program.

The spectral equidistribution conjecture turned out to be more subtle. The per-frequency fluctuations are not exactly equal at every frequency, but their weighted differences cancel under a Parseval-style identity that the moment theorem of [the collision spectrum](https://alexpetty.com/the-collision-spectrum/) makes precise. The "flat across the spectrum" picture I drew here is what holds in the limit. The note that immediately followed this one, on silent primes and the variance of the collision count, made the bound explicit.

The polarity equidistribution observation became the seed of [the polarity field](https://alexpetty.com/the-polarity-field/). The "field approaches its equilibrium on the fixed polarity circle" framing here is what the polarity field paper formalizes as the antisymmetric real-valued field that decomposes into odd Dirichlet characters. The three involutions that organize the program, $a \mapsto m - a$ on classes, $\chi \mapsto \bar\chi$ on characters, $s \mapsto 1 - s$ on the strip, all have their first quiet appearance in this paper as conjectures about equidistribution. They are the same symmetry operating at three levels, and that recognition came later.

The reason to care about this paper now is that it was the first time the program had a *layered* picture of the collision fluctuation rather than a flat one. Before this paper, the fluctuation was a single signal that I was trying to bound. After this paper, it was three orthogonal decompositions sitting on top of one structure, each carrying independent information. Every later piece of the program works with that layered picture in mind. The names changed, the proofs got tighter, but the architecture sketched here is the architecture the program runs on.

.:.

---

## Try it yourself

```
$ ./nfield character_components 10 --lag 1
  base 10, lag 1, modulus 10
  4 Dirichlet characters mod 10
  primes scanned: 1225
  trivial character |L_χ₀|: 1.393
  non-trivial:      |L_χ₁|: 0.398, |L_χ₂|: 0.350, |L_χ₃|: 0.398

$ ./nfield mertens_growth --base 10 --lag 1 --primes 10000
  Φ_x(1, 1) = -1.60
  Φ_x(1, 1) / log log p_max = -0.652
  drifting toward μ₁ ≈ 0.68

$ ./nfield spectral_fluctuation 10
  G(1, k) for k = 1 .. 5 in base 10:
  0.1651, 0.1651, 0.1650, 0.1646, 0.1644
  flat to three significant digits across the first five frequencies
```

Three commands, three views of the same fluctuation. The character split, the Mertens growth at the boundary, the spectral equidistribution. Run them on whichever base you like and watch the same shape come out.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Character Structure of the Collision Fluctuation](https://github.com/alexspetty/nfield/blob/main/research/collision_character_structure.pdf)

---

*Alexander S. Petty*
October 2022 (updated April 2026)
.:.
