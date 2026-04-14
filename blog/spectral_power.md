# The Spectral Power of the Digit Function

Every prime in base $10$ has a fingerprint, and the fingerprint is a list of ten integers.

Pick a prime $p$. Divide $1$ by it, then $2$, then $3$, up through $p - 1$, and look at the leading decimal digit of each fraction. Some leading digits appear once, some twice, some not at all. Group the residues by their leading digit. The number of residues in each group is what I will call a *bucket size*. There are ten buckets in base $10$, one for each possible leading digit, and the list of bucket sizes is the prime's fingerprint.

At $p = 7$, the bucket sizes are
$$(0, 1, 1, 0, 1, 1, 0, 1, 1, 0).$$
Six leading digits appear once each, the other four are empty. At $p = 13$, the buckets are
$$(1, 1, 1, 2, 1, 1, 2, 1, 1, 1).$$
Eight singletons and two doubled buckets. At $p = 29$ there are no zeros and no singletons; the bucket sizes settle into a mix of $2$s and $3$s. As $p$ grows, the bucket sizes drift toward an average of $p / 10$, but the way they drift depends on $p$ in a specific arithmetic way.

Those bucket sizes are the load-bearing data of the entire alignment program. [The alignment limit paper](https://alexpetty.com/the-alignment-limit/) showed the limiting alignment of a prime is determined by the sum of squared bucket sizes. [The spectral structure paper](https://alexpetty.com/the-spectral-structure-of-fractional-fields/) showed the eigenvalues of the cross-alignment matrix come from a Fourier transform that ultimately traces back to the bucket structure. Each invariant in the chain reaches into the bucket sizes for its raw material and pulls out a different summary.

None of those summaries is the natural object that contains them all. This paper builds the natural object. It is a function on the harmonics of the prime that takes a frequency as input and returns a number, and I call it the **spectral power** of the digit function. Every magnitude-side invariant of the alignment program is one of its values or one of its averages.

## Why "spectral power"

The name comes from signal processing. When you take an electrical signal, run it through a Fourier transform, and square the magnitude at each frequency, the resulting function is called the *power spectrum* or *spectral power* of the signal. It tells you how much of the signal's energy lives at each frequency. A pure tone has all its power at one frequency. A noisy signal has its power spread across many. The shape of the power spectrum is the harmonic identity of the signal.

I am borrowing the name because I am doing the same operation. Instead of a sound wave or an electrical signal, my signal is the bucket structure of the digit function: the indicator that says "this residue lives in bucket $d$ for digit $d$." Run that indicator through a Fourier transform, square the magnitude, and you get a function on harmonics that says how much of the bucket structure's energy lives at each frequency. That function is the spectral power of the digit function. I will write it $\Phi$ throughout this paper.

## Why this works at all

The reason the spectral power has a clean closed form is one of those small geometric facts that does big work.

Each bucket of the digit partition is a *run of consecutive residues*. It has to be, because the leading digit of $r/p$ moves up by one whenever $r$ crosses a multiple of $p / 10$, and otherwise stays put. So bucket zero is some run of small residues, bucket one is the next run, bucket two the next, and the runs march in order from small residues to large. The buckets do not jump around. They are intervals.

Intervals are the simplest possible sets to take a Fourier transform of. When you take a run of $n$ consecutive numbers and run them through a Fourier transform on a finite circle, the result is one of the oldest objects in classical harmonic analysis, the **Dirichlet kernel**. It dates back to Dirichlet's work in the 1830s on the convergence of Fourier series. It has a clean trigonometric closed form. It has been studied for nearly two centuries.

So the buckets in our digit partition do not produce just any kind of waves on the spectrum. They produce Dirichlet kernels, one per bucket, sized by how many residues the bucket contains. Sum the squared kernels across all the buckets, frequency by frequency, and you have the whole spectral power. That is the entire calculation, and the rest of this paper is just walking through what falls out of it.

## A function on the harmonics

There are $p$ harmonics in total at the prime $p$, the standard set you get when you do Fourier analysis on a finite cyclic group. The spectral power $\Phi$ takes one of these harmonics as input and returns a single number telling you how strongly the bucket partition resonates at that harmonic.

One harmonic is special, and the special one is the lowest. At the zeroth harmonic, every Dirichlet kernel collapses to its bucket size, because Fourier evaluation at frequency zero is just counting (a sum of $n$ ones is $n$). Square the contribution from each bucket and add over all the buckets, and you get
$$\Phi(0) = n_0^2 + n_1^2 + \ldots + n_{b-1}^2.$$
This is exactly the bin-sum that [the alignment limit paper](https://alexpetty.com/the-alignment-limit/) named $S(p, b)$. So the alignment limit is recovered, as it should be, from the lowest mode of the spectral power. The DC component of $\Phi$ is the old invariant in new clothing. It is the trivial mode of the new harmonic analysis the same way the diagonal of the cross-alignment matrix is the trivial pattern of the matrix.

For other frequencies, the spectral power is built one bucket at a time. Each bucket contributes a Dirichlet kernel whose shape depends on how many residues the bucket holds. Singletons contribute a flat constant at every frequency, the simplest possible shape. Buckets of size two contribute a small wave that peaks at the low frequencies and dies off at the high ones. Larger buckets contribute sharper waves with their own peaks and valleys. Sum the squared waves from every bucket and you have the whole spectral power.

The point is that $\Phi$ is the harmonic shadow of the bucket sizes. Tell me the bucket sizes, and I can hand you $\Phi$ at every frequency without doing any new work, just by adding up the bucket Dirichlet kernels.

## A worked example at $p = 13$

To make the picture concrete, take $p = 13$ in base $10$. [The spectral structure paper](https://alexpetty.com/the-spectral-structure-of-fractional-fields/) looked at this same prime from a different angle, by sorting its fractions into the two cosets that the multiplicative action of $\times 10$ generates. That decomposition is *multiplicative*. The bucket partition is *additive*. It asks which residues land in which leading-digit bucket under the floor function. The two decompositions of $p = 13$ live on the same set of residues but split it differently, and they highlight different things.

Look at the buckets directly.

```
digit 0:  {1}
digit 1:  {2}
digit 2:  {3}
digit 3:  {4, 5}
digit 4:  {6}
digit 5:  {7}
digit 6:  {8, 9}
digit 7:  {10}
digit 8:  {11}
digit 9:  {12}
```

Eight buckets of size one, two buckets of size two. The two doubled buckets are at digits three and six. They are the entire source of structure in the spectral power at this prime.

Compute $\Phi$ at frequency zero. Square every bucket size and add. Eight ones and two fours. Total sixteen. So $\Phi(0) = 16$, which is the bin-sum from the alignment limit paper, recovered as the value of the spectral power at the zeroth harmonic. The DC mode is the old invariant.

Now move to a nonzero frequency. The eight singleton buckets each contribute one, no matter what frequency you ask for. They are flat across the harmonics. The two doubled buckets each contribute a small wave whose height depends on the frequency. At the lowest nonzero frequency the wave is near its peak, and the doubled buckets push the spectral power up close to sixteen. Around the middle of the frequency range, the wave drops near zero and the doubled buckets vanish from the sum. The total drops to about eight, the contribution of the singletons alone. By symmetry, the wave climbs back up toward the top of the frequency range.

So the spectral power of $p = 13$ in base $10$ is a slow envelope. Sixteen at the DC mode, dropping to about eight in the middle, climbing back to sixteen at the top. The whole shape is set by the two doubled buckets fighting against the eight flat singletons.

There is a Parseval-style sanity check that the total spectral energy across all frequencies has to come out to a specific number, namely $156 = p (p - 1)$, and the slow envelope above adds up to exactly that. The harmonic accounting closes. A reader can verify this with a calculator in five minutes; it is the kind of computation that is small enough to fit on a napkin and yet contains the entire harmonic identity of the prime.

## What the spectrum tells you

The spectral power has three layers of meaning, and they line up neatly with three of the older invariants of the alignment program.

**The first layer is the alignment limit.** The DC mode of $\Phi$ is the bin-sum, and the bin-sum controls the limit of the alignment as the modulus grows. Everything the alignment limit paper said about that quantity is now a statement about a single coefficient of $\Phi$.

**The second layer is the digit-partitioning property.** A prime is digit-partitioning in a base if and only if its spectral power is constant in frequency. When every bucket has size one or zero, every nonempty bucket contributes the same flat constant at every harmonic, and $\Phi$ has no shape. It is white noise. Conversely, if $\Phi$ is constant, the buckets have to be singletons, which is exactly the digit-partitioning condition. Three different definitions of digit-partitioning, each living at a different level of the program, all turn out to be the same property in disguise.

**The third layer is the eigenvalue spectrum of the prime.** This is where $\Phi$ stops being enough, and it is where I plan to go next. The eigenvalues of the cross-alignment matrix are determined by an autocorrelation, and the autocorrelation depends on more than the loudness of the bucket harmonics. It also depends on their *timing*, on whether the harmonics are in step or out of step at related frequencies. The spectral power records the loudness only, because it was built by squaring, and squaring throws away the timing. My current line of attack is to introduce a richer object that keeps the timing and uses it to close the loop. We will see if it lands.

For now, what this paper has done is take the bucket sizes of a prime and turn them into a single function on the harmonics. The alignment limit lives at the lowest mode. The digit-partitioning property is the same as flatness. Everything else in the magnitude direction is also a contraction of the spectral power, and the spectral power itself is a sum of squared Dirichlet kernels weighted by the bucket sizes.

## A note from 2026

*April 2026*

This is the paper where the alignment program first learned to do harmonic analysis on the digit function instead of just counting the buckets. Before this paper, the program had the bucket sizes themselves and a handful of scalar combinations of them. After, the entire harmonic toolkit of the prime was available, and every later result in the chain used it.

The reason the toolkit became available at all is the small geometric fact that the buckets are runs of consecutive residues, because the digit function is monotone. Runs of consecutive residues have the simplest possible kind of harmonic content, a Dirichlet kernel, and Dirichlet kernels are objects classical analysis has known how to manipulate for nearly two centuries. So the buckets do not produce just any kind of waves on the spectral power; they produce a specific, very classical kind of wave that the rest of the alignment program could pick up and run with. The whole alignment program from this point forward is, at its core, the harmonic analysis of consecutive runs of integers.

That observation has consequences far beyond this paper. The autocorrelation formula in [the next paper](https://alexpetty.com/the-autocorrelation-formula/) takes the bucket waves and combines them into a richer object that turns out to be the right tool for computing the eigenvalue spectrum of the cross-alignment matrix. Several papers later, the same waves get restricted to special families of frequencies and produce identities of a kind first studied by Ramanujan. Much further on, the collision program at conductor $b^2$ uses the same wave identity to evaluate a different signal on the same bucket geometry. Every single one of those later moves traces back to the harmonic content of consecutive runs of integers, made explicit for the first time in this paper.

The interval geometry of the digit function is the load-bearing fact of the entire program. Everything else is built on top of it.

.:.

---

## Try it yourself

```
$ ./nfield spectral 11
  bucket sizes: 1,1,1,1,1,1,1,1,1,1
  Phi(0) = 10
  Phi flat at every frequency (digit-partitioning)

$ ./nfield spectral 13
  bucket sizes: 1,1,1,2,1,1,2,1,1,1
  Phi(0) = 16
  slow envelope, peaking at the DC mode and the top frequency

$ ./nfield spectral 29
  bucket sizes: 1,1,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1
  doubled buckets dominant
  Phi(0) = 56
```

At $p = 11$ the buckets are all singletons and the spectral power is perfectly flat. At $p = 13$ the two doubled buckets introduce a low-frequency bump. By $p = 29$ doubling has spread across most of the digit range, and the spectral power has real frequency structure that does not collapse to a single simple shape.

The thing to watch in the demos is the way the doubled buckets accumulate. The first doubled bucket appears at the smallest non-digit-partitioning prime in the base. Each successive prime adds more doubled buckets until the bucket sizes settle into a pattern that scatters around the average $p / b$. By the time $p$ is much larger than $b$, the buckets are small integers near $p / b$, and the spectral power has nontrivial bumps at every frequency. The shape of $\Phi$ is the harmonic profile of the prime in the base, computed without ever doing the long division.

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Spectral Power of the Digit Function](https://github.com/alexspetty/nfield/blob/main/research/spectral_power.pdf)

---

*Alexander S. Petty*
October 2021 (updated April 2026)
.:.
