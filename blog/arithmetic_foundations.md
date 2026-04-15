# Arithmetic Foundations

*January 2010*

## Breath

Here is a process most of us never think about:

The inflow of air from outside space into the lungs. Inward flow. With lungs fully expanded, the body is nourished with oxygen. The motion pauses briefly at the boundary before reversing direction. The outflow of air back into the surrounding space. Outward flow. With lungs depleted, the body begins to draw in again. The cycle reverses. The inward flow begins once more.

This rhythm of expansion and contraction, inward and outward, repeating continuously, is one of the most basic patterns in nature. During the course of exploring patterns in numbers I began to notice a similar kind of oscillation appearing in certain visualizations of arithmetic sequences. Not metaphorically. Structurally. The numbers expand outward along a path and then return along the mirror of that path, over and over.

I want to show what that looks like.

## Mapping numbers around a circle

The chart below lists the numbers 1 through 2016, placed on the radial spokes of a circle divided into nine parts. Each number lands on the spoke corresponding to its digital root (its value reduced modulo 9, with 9 replacing 0).

Each value is also shown with its base-10 digit compression. Whenever the digit sum crosses an order of magnitude, the color alternates between blue and gold, making the oscillation visible.

![Foundational table of arithmetic](https://alexpetty.com/content/images/2018/12/fae2016_small.png)

## Palindromic oscillations

On each radial spoke, the numbers follow a pattern that mirrors itself.

For example, on the 1 radial within the 500 range (values 505 through 595):

**Outward path:**

    505
    514
    523

**Mirror point, then inward path:**

    532  (32 mirrors 23)
    541  (41 mirrors 14)
    550  (50 mirrors 05)

**Second half:**

    559
    568
    577
    586  (86 mirrors 68)
    595  (95 mirrors 59)

The two-digit endings form palindromic pairs: 05/50, 14/41, 23/32, 59/95, 68/86. The sequence walks outward from the center of the range and then walks back along the mirror image.

This is not limited to one spoke or one range. It appears on every radial, in every range, throughout the entire table. The pattern completes a full cycle after 223 rotations around the circle of nine.

The palindromic structure is a consequence of how digit sums behave under incrementation. When you add 9 to a number, its digital root does not change, but its digits rearrange. The rearrangement follows a path that is symmetric around the midpoint of each range. The symmetry is built into the place-value system itself.

## Circular visualization

When the same data is plotted on a circular system, the numbers form interlaced spiral patterns.

![Foundational arithmetic, 1x](https://alexpetty.com/content/images/2018/12/fns-circle-chart-round-1x1.png)

The spiral paths expand outward and then contract back toward the center, producing a visual oscillation within the structure. One arm of the spiral grows while another returns. The result looks like breathing.

![Breath of the spiral](https://alexpetty.com/content/images/2018/12/breath-1.png)

I do not think the resemblance to respiration is an accident. Expansion and contraction around a fixed center, with a pause at each boundary before reversal, is a pattern that appears at many scales in nature. Finding it inside the integers suggests that the pattern is more fundamental than any particular physical system that exhibits it.

## Magnified views

Looking closer at the system reveals finer spiral structures nested within the larger ones. The same oscillating pattern repeats at every level of magnification.

### 2x magnification

![2x](https://alexpetty.com/content/images/2018/12/fns-circle-chart-round-2x.png)

### 4x magnification

![4x](https://alexpetty.com/content/images/2018/12/fns-circle-chart-round-4x.png)

### 6x magnification

![6x](https://alexpetty.com/content/images/2018/12/fns-circle-chart-round-6x.png)

### 8x magnification

![8x](https://alexpetty.com/content/images/2018/12/fns-circle-chart-round-8x.png)

### 16x magnification

![16x](https://alexpetty.com/content/images/2018/12/fns-circle-chart-round-16x.png)

### 32x magnification

![32x](https://alexpetty.com/content/images/2018/12/fns-circle-chart-round-32x.png)

At each magnification the same kind of structure appears: interlaced spirals, palindromic paths, the same expansion and contraction. The pattern does not break down at finer scales. It persists.

## Vortex representation

Overlaying the spiral structure with the vortex glyph from my [earlier post](https://alexpetty.com/on-numeric-polarity-and-the-distribution-of-primes/) highlights the rotational flow in the system.

![Foundational arithmetic with vortex glyph](https://alexpetty.com/content/images/2018/12/fns-circle-chart-round-with-vortex-glyph.png)

The glyph and the spiral align. The structural roles of 3, 6, and 9 as organizing poles of the ninefold cycle are visible here as the axes around which the spiral paths turn.

## Primes on the spiral

When prime numbers are highlighted on the same structure, they occupy specific paths within the spiral system.

![Primes on foundational arithmetic](https://alexpetty.com/content/images/2018/12/fns-circle-chart-primes.png)

![Magnified view of primes](https://alexpetty.com/content/images/2018/12/fns-circle-chart-primes-zoom-1.png)

The primes avoid the 3, 6, and 9 spokes (as expected) but within the remaining spokes they do not distribute uniformly. They cluster along certain arms of the spiral and thin out along others. The spiral representation makes these density variations visible in a way that a linear list of primes does not.

## What this shows

Simple arithmetic sequences, when viewed through circular and rotational mappings, produce structured patterns of surprising richness. The palindromic oscillation on each radial spoke, the interlaced spirals, the self-similar structure at multiple magnifications, and the non-uniform distribution of primes within the spiral are all consequences of how the place-value system interacts with modular arithmetic.

The breathing analogy is the part of this post that I keep returning to. The integers expand outward through each range and then contract back along the mirror path, cycling through the same bounded set of digital roots, over and over. The motion is internal. The boundary is fixed. And the pattern is the same at every scale I have examined.

.:.

---

## A note from 2026

*April 2026*

The palindromic oscillation here is the complement map. The outward path and the inward path are $k$ and $m - k$, two residues that sum to the modulus, walking in opposite directions through the same range. I did not have those words in 2010, but the structure I was drawing was the same one that later produced the antisymmetry $F(a) + F(m - a) = 0$ in the polarity field.

The breathing is more precise than I realized. The polarity field cancels in the first moment across primes. The positive and negative contributions wash out. But it persists in the second moment, where the amplitude is constant. Expansion and contraction that never settles and never escapes. That is what these spirals are showing. The field breathes because complement pairs force cancellation in the sum while preserving energy in the variance.

The self-similarity at every magnification pointed toward something I could not have anticipated. The the sawtooth identity holds at every base and every prime, and the structure it produces is the same at every scale because the digit function $\delta(r) = \lfloor br/p \rfloor$ is scale-invariant by construction. The nested spirals in these diagrams are the visual trace of that invariance.

The primes tracking certain arms of the spiral and avoiding others is the collision periodic table in embryonic form. Each arm of the spiral corresponds to a residue class, and the density of primes along each arm is governed by the collision invariant $S(p)$ assigned to that class. The non-uniform distribution I noticed here became the central object of [the alignment limit for all primes](https://alexpetty.com/the-alignment-limit-for-all-primes/) and the work that followed it.

.:.

---