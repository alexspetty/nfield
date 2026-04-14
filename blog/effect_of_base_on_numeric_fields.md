# Effect of Base on Numeric Fields

*August 2010*

## A simple investigation into base and modular patterns

Today I have been investigating how number systems behave when expressed in different bases.

While experimenting with sequences generated in different bases and examining them under modular reduction, I began to notice a pattern. Regardless of which base was used, the resulting sequences often formed a kind of mirrored structure. The values would move outward and then return inward in a symmetrical fashion.

This suggested that the structure might not be tied to any particular base, but instead might be a property of the relationship between a base and its modulus.

To explore this further I generated number sequences using the following pattern:

Base *n* mod (*n* - 1)

For example:

- Base 9 mod 8
- Base 8 mod 7
- Base 7 mod 6
- Base 6 mod 5
- Base 5 mod 4
- Base 4 mod 3
- Base 3 mod 2
- Base 2 mod 1

For each of these systems I computed the first 33 increments and plotted the results.

To make the patterns easier to visualize:

- Red indicates expansion or outward movement (+)
- Gray indicates contraction or inward movement (-)

When the sequences are visualized this way, something interesting becomes visible. The paths produced by the sequences form mirrored palindromes. The numeric field expands outward from a center point and then returns along a symmetric path.

## What changes and what does not

What strikes me most about these patterns is not the motion itself but what stays the same through it.

The sequences swirl outward and collapse inward, tracing different paths depending on the base. The internal dynamics change. A base-9 field produces a rich, multi-layered oscillation. A base-3 field produces a simpler one. But in every case the system's extent, its circular boundary, remains the same. The field breathes, but it does not grow or shrink.

This is a consequence of modular reduction. No matter how large the integers become, the modulus maps them back into the same bounded set of residues. The system is confined to a fixed space. What changes is the path the sequence traces through that space, not the space itself.

The outward path and the inward path are mirror images of each other. They are complements. Their sum is always the modulus. So the expansion and contraction are not independent motions. They are two views of the same structure, one counting up from the center and the other counting down, and they balance exactly.

I find this worth sitting with. The dynamics change. The boundary does not. Something is preserved through all of the internal motion, and I think that something matters.

The simplest case makes this clearest. In base 2 mod 1, there is only one possible residue. The system has no room to move at all. Pure stillness.

The moment a third state is introduced, motion begins. The system starts to oscillate between expansion and contraction.

As more states are added, the internal dynamics become richer. More paths, more oscillations, more elaborate palindromes. But the boundary holds. The identity persists. It is the same system seen at different resolutions.

## Numeric fields across different bases

Below are the charts generated for each base system. Each chart shows the first 33 values produced under the base/modulus relationship described above.

Red paths represent outward movement in the sequence. Gray paths represent the inward return. Together they reveal the mirrored structure of the numeric field.

Look at how the patterns change as the base decreases. The higher bases produce complex, layered oscillations with many internal crossings. As the base shrinks, the patterns simplify, but the symmetry remains. By the time we reach base 2 the field has collapsed to a single point. The motion is gone, but the structure that generated it is still present.

## Base 9 mod 8

![Table](https://alexpetty.com/content/images/2018/12/base9mod8-fns-table1-1.png)

![Chart](https://alexpetty.com/content/images/2018/12/base9mod8-fns-web1.png)

Nine states produce the richest field in this set. The palindromic paths cross and recross, forming a layered web of outward and inward motion. But count the distinct residues: there are still only eight. The complexity is in the path, not in the space.

## Base 8 mod 7

![Table](https://alexpetty.com/content/images/2018/12/b8m7-fns-table.png)

![Chart](https://alexpetty.com/content/images/2018/12/base8mod7-fns-web1.png)

## Base 7 mod 6

![Table](https://alexpetty.com/content/images/2018/12/b7m6-fns-table.png)

![Chart](https://alexpetty.com/content/images/2018/12/base7mod6-fns-web-1.png)

## Base 6 mod 5

![Table](https://alexpetty.com/content/images/2018/12/b6m5-fns-table-1.png)

![Chart](https://alexpetty.com/content/images/2018/12/b6m5-fns-web.png)

## Base 5 mod 4

![Table](https://alexpetty.com/content/images/2018/12/b5m4-fns-table.png)

![Chart](https://alexpetty.com/content/images/2018/12/b5m4-fns-web.png)

## Base 4 mod 3

![Table](https://alexpetty.com/content/images/2018/12/b4m3-fns-table.png)

![Chart](https://alexpetty.com/content/images/2018/12/b4m3-fns-web.png)

Three residues. The pattern is becoming sparse, but the palindromic structure is still clearly visible. Outward, then inward. Always balanced.

## Base 3 mod 2

![Table](https://alexpetty.com/content/images/2018/12/b3m2-fns-table.png)

![Chart](https://alexpetty.com/content/images/2018/12/b3m2-fns-web.png)

Two residues. The simplest possible oscillation: out, in, out, in. A single alternation, repeated.

## Base 2 mod 1

![Table](https://alexpetty.com/content/images/2018/12/b2m1-fns-table.png)

![Chart](https://alexpetty.com/content/images/2018/12/b2m1-fns-web.png)

One residue. The system has collapsed to a point. There is nowhere to go. This is the identity itself, with no motion to express it.

## Observations

Across every base examined, the numeric field produces the same kind of structure.

The sequences expand outward and contract inward along mirrored paths. The base determines the resolution, how many states the system has to work with, how many layers the palindrome contains. But the palindromic structure itself is invariant. It does not depend on the base.

What I keep coming back to is the relationship between the internal motion and the boundary. The paths wind through the available states in increasingly complex ways as the base grows. But the circular area of the field, the total extent of the residue space, never changes for a given modulus. The dynamics change. The boundary does not.

I think this is saying something about how number systems work at a level beneath the choice of base. The base is a lens. It determines how much detail you see. But the structure you are looking at is the same structure regardless.

.:.

---

## A note from 2026

*April 2026*

The palindromic symmetry in these charts is the complement map. The pair $k$ and $n - k$ trace mirror paths through the residue space. The "outward and inward" motion is the same pairing that produces the antisymmetry $F(a) + F(m - a) = 0$ in the [polarity field](https://alexpetty.com/the-polarity-field/). I was watching it happen in 2010, long before I formalized its name in rigorous mathematics.

The observation that the pattern is base-independent turned out to be one of the most important things in the entire early sequence. The [sawtooth identity](https://alexpetty.com/the-polarity-field/) $G_{b,q,k}(\chi) = bq^{k-1} B_1(\chi)$ holds at every base $b$ and every prime $q$ simultaneously. The base determines the internal dynamics of the digit function, how remainders sort into bins, which collisions occur. But the Bernoulli number on the right side does not depend on $b$ at all. The base is a lens, as I wrote here. The structure it reveals is universal.

The line "the dynamics change, the boundary does not" is the closest I came in 2010 to stating what the later work proves. The digit function changes with the base. The collision spectrum changes. The individual Fourier coefficients change. But the polarity field's cancellation across primes, its convergence at $s = 1$, its antisymmetry under the complement map, none of that depends on which base you chose to look through. The boundary holds.

.:.

---

*Base 2 mod 1. One residue, nowhere to go. Concentric rings of red and grey pulse outward from the center, but every ring maps to the same point. The identity itself, before motion begins.*
