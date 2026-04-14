# Foundational Tables of Multiplication

*January 2010*

Can numbers reveal additional structure when we change the way we look at them?

The arithmetic of integers is extremely well understood, but sometimes a shift in representation makes familiar relationships appear in new ways. In the following diagrams, multiplication tables are visualized on circular and spiral coordinate systems rather than the usual rectangular grids.

This does not change the mathematics itself, but it can make certain patterns easier to see. And some of what becomes visible is, I think, worth the effort.

## Digits and positional arithmetic

In 1202 AD, Fibonacci described the positional numeral system in his Liber Abaci:

> "These are the nine figures of the Indians: 9 8 7 6 5 4 3 2 1. With these nine figures, and with this sign 0 which in Arabic is called zephirum, any number can be written."

These ten symbols form the basis of the modern decimal system. Every number we work with is built from them. What follows is an exploration of what happens when we take the most elementary operation on these symbols, multiplication, and watch how it moves through a circular coordinate system.

## The number line

The standard model for the integers is the number line, where numbers are arranged along a single axis.

![The number line](https://alexpetty.com/content/images/2026/03/numberline.png)

The number line is extremely useful for understanding addition, subtraction, and ordering. But when we move into multiplication, periodicity and modular structure begin to play a larger role. The line hides cycles. A circle reveals them.

## Spiral arrangements

One way to bridge the two is a spiral: a number line that curves back on itself at regular intervals.

![Numeric spiral](https://alexpetty.com/content/images/2018/12/numeric-spiral1.png)

Spiral layouts are commonly used in mathematics and physics when studying growth processes or rotational symmetries. Here the spiral serves as a coordinate system for plotting arithmetic relationships, combining the linear order of the number line with the cyclic structure of modular arithmetic.

## The standard multiplication grid

Multiplication tables are usually displayed as a rectangular grid.

![Tables of multiplication](https://alexpetty.com/content/images/2018/12/tables-of-multiplication.png)

This grid clearly shows the growth relationships between numbers. But it hides something: the cyclic behavior that emerges when we examine multiplication modulo a fixed base. Every multiplication table, extended far enough, repeats. The grid does not show the repetition. It just keeps growing to the right.

## Multiplication on a circular system

If we take the same multiplication tables and plot them on a circle divided into nine radial positions (modulus-9 arithmetic), the sequences begin to trace distinct paths.

![Foundational tables of multiplication](https://alexpetty.com/content/images/2018/12/foundational-tables-of-multiplication.png)

Each multiplication table generates its own repeating cycle. The cycle lengths vary: some tables produce short loops, others visit many positions before returning to their starting point. But every table eventually returns. That is the nature of modular arithmetic.

From this representation we can derive a general structural diagram showing how all multiplication sequences move through the circular system.

![Universal structure of geometric growth](https://alexpetty.com/content/images/2018/12/universal-structure-of-geometric-growth.png)

## Flow signatures of the multiplication tables

When plotted on the circle of nine, each digit from 1 through 9 produces a characteristic trajectory. Some of these are simple. Some are surprisingly complex. Together they reveal the full geometry of multiplication in the decimal system.

### The one's table

![Ones](https://alexpetty.com/content/images/2018/12/ones-table-chart-.png)

The identity. Every multiple of 1 is itself. The sequence walks around the circle visiting every position in order: 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, ...

### The two's table

![Twos](https://alexpetty.com/content/images/2018/12/twos-table-chart-1.png)

The doubling sequence. Under digital root reduction it produces the cycle 2, 4, 8, 7, 5, 1, then repeats. Six distinct positions visited before the pattern closes. This is the same cycle that appeared in the [field glyph of 4](https://alexpetty.com/geometries-hidden-in-the-number-system/) and in the vortex diagrams.

### The three's table

![Threes](https://alexpetty.com/content/images/2018/12/threes-table-chart-1.png)

The multiples of three form a repeating triangular path: 3, 6, 9, 3, 6, 9, ... Only three positions, cycling forever. This is the closed polar loop from the [circle of nine](https://alexpetty.com/on-numeric-polarity-and-the-distribution-of-primes/).

### The four's table

![Fours](https://alexpetty.com/content/images/2018/12/fours-table-chart-.png)

The four's table traces the same six positions as the two's table, but in a different order: 4, 8, 3, 7, 2, 6. It is the doubling cycle entered at a different point.

### The five's table

![Fives](https://alexpetty.com/content/images/2018/12/fives-table-chart-1.png)

Five is the turning point. Up to this point the multiplication cycles trace the circle in one direction. Beyond five they reverse and begin tracing the circle in the opposite orientation. This makes sense: 5 is one less than half of the cycle length (9), and in modular arithmetic, multiplication by *n* and multiplication by (modulus − *n*) produce mirror-image paths.

### The six's table

![Sixes](https://alexpetty.com/content/images/2018/12/sixs-table-chart-.png)

The six sequence mirrors the three sequence but travels in the opposite direction: 6, 3, 9, 6, 3, 9, ... The same triangle, reversed. Three and six are complements, and their multiplication paths are complements too.

### The seven's table

![Sevens](https://alexpetty.com/content/images/2018/12/sevens-table-chart-1.png)

Seven mirrors two. The cycle visits the same six positions as the doubling sequence, but in reverse order.

### The eight's table

![Eights](https://alexpetty.com/content/images/2018/12/eights-table-chart-1.png)

Eight mirrors one. Its sequence walks around the circle visiting every position, but in the opposite direction: 8, 7, 6, 5, 4, 3, 2, 1, 9, 8, 7, ...

### The nine's table

![Nines](https://alexpetty.com/content/images/2018/12/nines-table-chart-.png)

Under modulus-9 arithmetic, all multiples of nine reduce to 9 (equivalently, to 0). The sequence maps repeatedly to the center of the circle. Nine is the identity element of the digital root system. It absorbs everything.

## The mirror structure

A pattern has emerged. The multiplication tables come in complementary pairs:

- 1 and 8 (full circle, opposite directions)
- 2 and 7 (six-position cycle, opposite directions)
- 3 and 6 (triangular loop, opposite directions)
- 4 and 5 (six-position cycle, opposite directions)
- 9 stands alone (collapses to the center)

Each pair sums to 9. The second half of the multiplication tables is a mirror image of the first half. This is not a coincidence. It is a direct consequence of the fact that multiplication by *k* mod 9 and multiplication by (9 − *k*) mod 9 produce sequences that are reversals of each other.

## Universal structure

All of these patterns arise from the same underlying network of multiplicative cycles.

![Universal structure with arrows](https://alexpetty.com/content/images/2018/12/arrows-ver-universal-structure-of-geometric-growth.png)

When viewed together, the multiplication sequences form a network of repeating loops. The network has a definite architecture: the 3-6-9 triangle at the center, the 1-2-4-8-7-5 hexagon around it, and the reversal symmetry connecting opposite sides.

![Vortex glyph](https://alexpetty.com/content/images/2018/12/vortex-glyph-2.png)

This summary diagram captures the same relationships in a compressed form. It is the same glyph that keeps appearing throughout these investigations, arising here from a completely different starting point: not from modular reduction of integers, but from the cyclic structure of multiplication itself.

## Numeric relationships

The circular representation reveals several symmetries at a glance.

![Numeric polarity](https://alexpetty.com/content/images/2018/12/numeric-polarity.png)

The sequences generated by 3 and 6 mirror each other. The digit 9 acts as the identity element. And the six-position doubling cycle 1, 2, 4, 8, 7, 5 forms the backbone of the system, the longest possible orbit for a single multiplication table in mod-9 arithmetic.

## Doubling and halving cycles

If we follow the digital roots produced by repeated doubling, we obtain a cycle:

**Doubling:**

    1 → 2 → 4 → 8 → 7 → 5 → 1

The sequence repeats after six steps. Every power of 2, no matter how large, has a digital root drawn from this set of six values.

**Halving:**

    1 → 5 → 7 → 8 → 4 → 2 → 1

The halving cycle is the doubling cycle reversed. This is the mirror symmetry again: doubling is multiplication by 2, halving is multiplication by 5 (since 2 × 5 = 10 ≡ 1 mod 9), and 2 and 7 are complements while 5 and 4 are complements.

## Observations

Multiplication tables are usually presented as rectangular grids, and in that form they look like growth without structure. When the same arithmetic is mapped onto a circular coordinate system, the growth reveals itself as motion through a repeating geometric pattern.

The key observation is the mirror structure. The first half of the multiplication tables and the second half are reflections of each other, connected by the complement relationship *k* + (9 − *k*) = 9. This is the same complement symmetry that appeared in the [palindromic oscillations](https://alexpetty.com/arithmetic-foundations/) of the foundational arithmetic table and in the [polarity assignments](https://alexpetty.com/on-numeric-polarity-and-the-distribution-of-primes/) of the circle of nine. It keeps showing up because it is built into the structure of the decimal system at the deepest level.

It is also worth noting that there is nothing inherently special about base 10 here. Any base will produce its own modular cycles and geometric patterns. The symmetries arise from the relationship between a base and its modulus, not from the specific digits involved. However, because our arithmetic is built around base 10, the patterns that emerge from decimal modular arithmetic are the ones most natural for us to explore.

.:.

---

## A note from 2026

*April 2026*

The mirror structure described here, where multiplication by $k$ and multiplication by (modulus $- k$) produce reversed paths, is the complement map $a \mapsto m - a$ that became the foundation of the later work. In the [fractional field](https://alexpetty.com/why-the-golden-ratio-selects-the-prime-three/) $\{k/n\}$, the fraction $k/n$ and its complement $(n - k)/n$ sum to $1$, and their repetends are digit-by-digit complements. The same pairing, lifted to residue classes modulo $b^2$, forces an exact antisymmetry on the collision invariant: $F(a) + F(m - a) = 0$. The the polarity field is what that antisymmetry produces.

The two structures visible on the circle of nine, the 3-6-9 triangle and the 1-2-4-8-7-5 hexagon, turned out to correspond to something precise. The triangle is the additive subgroup, closed under addition mod $9$. The hexagon is the multiplicative orbit of $2$ mod $9$. In the language of the later work these became *force* and *form*: the radial scaffold and the transverse flow. Their independence, the fact that membership in one tells you nothing about position in the other, is what prevents the polarity field from accumulating coherently across primes. That independence is the mechanism behind the avoidance.

The six-position doubling cycle $1, 2, 4, 8, 7, 5$ is the multiplicative order $\text{ord}_9(2) = 6$. In the later work, $\text{ord}_p(b)$ determines the repetend length and governs the [alignment limit](https://alexpetty.com/the-alignment-limit-for-all-primes/) for each prime.

The line I wrote here in 2010, "any base will produce its own modular cycles," turned out to be more important than I knew. The the sawtooth identity holds at every base and every prime simultaneously. The patterns on the circle of nine are not special to base ten. They are universal.

.:.

---

*The five's table on the circle of nine. The turning point, where multiplication reverses direction and the star pattern crosses through every position. Growth without structure on the grid. Motion through geometry on the circle.*
