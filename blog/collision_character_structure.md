# The Character Structure of the Collision Fluctuation

I added up the collision deviations for every prime in base 10 up to a cutoff, weighted by $1/p$. The sum drifted downward. Not fast. Unimaginably slowly. The rate turned out to be $\log \log x$, the iterated logarithm, one of the slowest-growing functions in analysis. Between a million and a trillion, it increases by less than one.

But the drift had structure. It was not a single stream. When I split the primes by their last digit, four parallel currents appeared, each carrying its own share of the drift. This paper takes that observation and works out what each current carries.

The splitting is proved. What comes out the other side is mostly conjecture supported by computation.

## Splitting the signal

In base $10$, every prime past $5$ ends in one of four digits. $1$, $3$, $7$, or $9$. Each one is a *residue class modulo $10$*, which is just a fancy way of saying "the set of all numbers that share the same last digit in base ten". The primes ending in $1$ form their own subsequence inside the primes. So do the primes ending in $3$, in $7$, in $9$. Four parallel streams of primes, sorted by last digit.

The natural question, given that we want to split a sum across primes, is whether the four streams contribute differently to the total. Maybe primes ending in $1$ do most of the work and primes ending in $9$ barely matter. Or maybe the four streams contribute equally and the total is just four copies of the same thing. Or maybe the truth is somewhere in between, with each stream carrying its own characteristic signal.

The tool for sorting this out has been around since $1837$, when Dirichlet invented it to prove that every residue class has infinitely many primes. The tool is called a *Dirichlet character*. The name is heavy, but the idea is light.

A Dirichlet character is a recipe for assigning a small complex number to each residue class, with one rule. The number assigned to a product of two classes has to equal the product of the numbers assigned to each. So if a character assigns the value $i$ (the imaginary unit) to the class of primes ending in $3$, and the value $-1$ to the class ending in $7$, then it must assign $-i$ to the class ending in $1$, because $3 \times 7 = 21$ ends in $1$ and the values have to multiply correctly. The character *respects multiplication*, in that sense. It is a way of weighting the four classes that plays nicely with how the classes combine.

How many such recipes exist in base ten? Exactly four. The count is given by a number-theoretic function called *Euler's totient*, written $\varphi(b)$, which counts the residues mod $b$ that are coprime to $b$. In base ten the coprime residues are $\{1, 3, 7, 9\}$, so $\varphi(10) = 4$, and the number of Dirichlet characters mod $10$ is also four. One of the four characters is the *trivial* character, which assigns the value $1$ to every class. The other three are non-trivial, assigning different complex weights to the four classes in ways that respect multiplication.

These four characters do for the residues coprime to $10$ what sines and cosines do for periodic signals on the real line. They form an *orthogonal basis*, which means any function defined on the four classes can be uniquely expanded as a weighted sum of the four characters. The trivial character carries the average of the function across all four classes. The non-trivial characters carry the corrections, the part that says how much each class deviates from the average.

Apply this to the collision fluctuation. For each character $\chi$ mod $b$, take the fluctuation $\Delta_p$ at each prime $p$, multiply it by $\chi(p)$ (the character's complex weight on that prime's residue class), divide by $p^s$ (a damping factor that makes large primes count less, with the *exponent* $s$ as a knob we get to vary), and add up over all primes past the base, up to a cutoff $x$:

$$L_{\chi,x}(s, \ell) = \sum_{b < p \le x} \frac{\chi(p) \cdot \Delta_p(\ell)}{p^s}.$$

Four characters, four sums. Each one measures how the collision fluctuation behaves on the residue classes that character emphasizes.

The proposition that ties everything together is short. **At each finite cutoff $x$, the fluctuation taken only over primes in a single residue class $r$ is a finite linear combination of the four character components**, with weights $\overline{\chi}(r) / \varphi(b)$ where $\overline{\chi}$ is the complex conjugate of $\chi$. This is just the orthogonality of Dirichlet characters applied to the partition of primes by residue class. It is the same identity Dirichlet used in $1837$ to prove there are infinitely many primes in every coprime class. Here it is applied to a different signal, the collision fluctuation, but the algebra is the same. It is the only proved result in this paper, and everything else hangs on it.

## Four components in base ten

Compute the four character components numerically and see what they look like. Here is the table from the underlying research note, base $10$ at lag $\ell = 1$, walking up through primes:

```
$ ./nfield character_components 10 --lag 1

primes ≤ x    |L_χ₀,x| |L_χ₁,x| |L_χ₂,x| |L_χ₃,x|
----------    -------  -------  -------  -------
   100        1.073    0.254    0.321    0.254
   500        1.278    0.356    0.350    0.356
   800        1.341    0.380    0.355    0.380
  1225        1.393    0.398    0.350    0.398
```

Each column is one of the four characters. The trivial character $\chi_0$ weights every class equally. The other three carry the corrections. All four magnitudes grow as we add primes. The trivial character $\chi_0$ carries the largest weight by some margin, climbing past $1.4$ by the time we have a thousand primes in the sum. The three non-trivial characters carry smaller weights, around $0.35$ to $0.40$ apiece. The characters $\chi_1$ and $\chi_3$ are *complex conjugates* of each other (one is built from $i$ where the other has $-i$), and conjugation preserves magnitudes, so $|L_{\chi_1,x}| = |L_{\chi_3,x}|$ exactly. The table confirms this on every row, all the way down.

![Four character components of the collision fluctuation](https://alexpetty.com/content/images/2026/04/post12_four_components.png)

All four components appear to be growing at the same rate, the same $\log \log x$ creep. The trivial character carries the bulk of the signal because it averages the fluctuation across all classes with equal weight. The non-trivial characters carry the per-class corrections, the part that says how much each residue class deviates from the average. They are smaller in magnitude but they grow at the same rate.

This is one piece of the wonder. The collision fluctuation does not concentrate in one residue class. It spreads across all four, with each class carrying a character-specific weight, and all four weights grow at the same rate at the boundary.

## Not the classical L-values

The natural hope was that the character components would turn out to be the classical Dirichlet $L$-values in disguise. That would have been the cleanest answer. For each character $\chi$, classical number theory defines an infinite series,

$$L(s, \chi) = \sum_{n = 1}^{\infty} \frac{\chi(n)}{n^s},$$

which sums the character's values across all positive integers, weighted by $1/n^s$. At the special exponent $s = 1$, this series converges to a specific number, $L(1, \chi)$. These special values $L(1, \chi)$ govern how primes distribute across residue classes — they are the quantities Dirichlet himself studied to prove the prime infinitude theorem in $1837$, and they have been one of the central objects of analytic number theory ever since. So if our new character components $L_\chi(s, \ell)$ are proportional to $L(1, \chi)$ at $s = 1$, that would be the cleanest possible answer. The new objects would be the old objects in disguise.

They appear not to be. In base $10$ at lag $\ell = 1$, the underlying research note computes the truncated ratios

$$\frac{|L_{\chi_2,x}(1, 1)|}{|L(1, \chi_2)|} \approx 0.54, \qquad \frac{|L_{\chi_1,x}(1, 1)|}{|L(1, \chi_1)|} \approx 0.40.$$

The numerators are the magnitudes of our character components from the previous section. The denominators are the magnitudes of the classical $L$-values at the same characters. The ratios should be constants if the two are proportional. They are not. They are not simple rational numbers (they do not look like $1/2$ or $2/3$ or anything clean), they depend on the lag $\ell$ (changing $\ell$ moves the ratio), and they change shape from base to base.

So the character components are something new. They live in the same space the classical $L$-functions live in, built from the same Dirichlet characters, but they carry information the classical objects do not encode. The collision fluctuation had produced a new family of arithmetic objects. I did not yet know what they were made of. That would take three more years.

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

At $s = 1$, every base gives a partial sum near $-1.3$ to $-1.4$, growing at the Mertens rate. At $s = 0.9$, every base diverges. The critical boundary sits at $s = 1$ in every base I tested.

The specific numbers depend on the base. The qualitative structure does not. Slow drift at $s = 1$, fast divergence below. Five bases, the same shape. This is the universality conjecture. It is supported by computation. It is not proved.

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

Five different frequencies, five different sums, all converging to nearly the same value, around $0.165$. In the tested range, the collision fluctuation appears to distribute its energy *evenly across the spectrum*. No harmonic mode seems to dominate. The chord drifts, but it drifts almost uniformly at every frequency.

This is the spectral equidistribution conjecture. Computation in base $10$ shows convergence to within a few digits across the first five frequencies. Whether this holds at every frequency, and whether the limiting value has a closed form, are open questions.

## Around the polarity circle

There is a third axis of structure, and it comes from a different kind of observable.

The cumulative polarity of the repetend traces a path on the fixed circle of residues modulo $b - 1$. At each position of the repetend, the running digit sum modulo $b - 1$ takes one of $b - 1$ values. Count how many positions land on each value. The result is the polarity histogram, a vector of $b - 1$ counts that records how the field is distributed around its polarity circle.

For primes where $b$ is a primitive root, the polarity histogram appears to approach the uniform distribution as $p$ grows. The path visits each value approximately $L/(b-1)$ times. The polarity circle is the limiting equilibrium, and the field approaches it.

The collision fluctuations measure departure from this equilibrium. The Mertens growth law asserts that the departures, weighted by $1/p$, accumulate at rate $\log \log x$. The spectral equidistribution conjecture says the departures are nearly flat across the harmonic spectrum. Together, these observations suggest that the field approaches its equilibrium on the fixed polarity circle, and that the rate of approach is controlled by the critical boundary $s = 1$.

This is observational. None of the polarity statements are proved here. They are the third leg of the same structural conjecture, sketched in the underlying research note as a piece of the landscape that needs its own paper to formalize.

## Three decompositions, one boundary

The collision fluctuation admits three independent decompositions.

**By Dirichlet character.** Sort the primes by their last digit and the sum splits into one clean component per residue class. In base ten, four classes, four components. The split is [proved](https://github.com/alexspetty/nfield/blob/main/research/collision_character_structure.pdf).

**By harmonic frequency.** Sort by which eigenvalue of the cross-alignment matrix the prime is sitting on, and the weight spreads evenly across all the eigenvalues. Every frequency carries the same drift. The split is conjecture.

**By polarity.** Sort by where each prime's running digit sum lands on the polarity circle, and the distribution is uniform around the circle. Every position on the circle gets the same share. The split is observational.

Three decompositions of the same sum. The first cares about the arithmetic of residues. The second cares about the eigenvalues of a matrix. The third cares about the geometry of digit sums on a circle. They share no machinery and live in three different mathematical spaces.

Each of the three points to the same critical boundary at $s = 1$ in the current computations. The character components appear to grow logarithmically at that boundary. The frequency fluctuations appear to converge there. The polarity equidistribution appears to set in at a rate controlled by the same exponent. Three independent decompositions, all pointing at the same critical exponent.

![Three decompositions, one boundary](https://alexpetty.com/content/images/2026/04/post12_three_decompositions.png)

The collision fluctuation has structure. I intend to develop it.
## A note from 2026

*April 2026*

Almost every conjecture in the body got upgraded to a theorem in the work that followed. The character decomposition became the central technical move. By [the collision spectrum](https://alexpetty.com/the-collision-spectrum/), the same orthogonality argument was being applied to the collision invariant table itself, and the "new family of arithmetic objects" turned out to be the elementary side of a Bernoulli-L-value formula whose Fourier coefficients factor as $B_1(\bar\chi) \cdot S_G(\chi) / \varphi(b^2)$. None of that was visible from here. It needed three more years.

The spectral equidistribution conjecture turned out to be more subtle than "flat across the spectrum." The per-frequency differences cancel under a Parseval-style identity in [the collision spectrum](https://alexpetty.com/the-collision-spectrum/). The polarity equidistribution observation became the seed of the polarity field, where the three involutions ($a \mapsto m - a$, $\chi \mapsto \bar\chi$, $s \mapsto 1 - s$) that first appear here as conjectures are recognized as the same symmetry at three levels.

Before this work, the fluctuation was a single signal. After it, three orthogonal decompositions, each carrying independent information.

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
