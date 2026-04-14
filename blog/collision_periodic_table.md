# The Collision Periodic Table

Every prime number past 100, in base 10, has a single small integer attached to it. The integer is determined entirely by the prime's last two digits. There are forty possible "last two digits" for a prime (the integers between 1 and 99 that are coprime to 10), and so there are exactly forty integers in this table. Every prime past 100, no matter how large it gets, sits on top of one of those forty cells.

The prime $109$ produces the integer $+8$. So does the prime $50{,}009$. So does the prime $1{,}000{,}009$. All three end in $09$, so all three carry the fingerprint stamped onto class $09$.

The prime $191$ produces the integer $-9$. So does the prime $491$. So does the prime $99{,}999{,}991$. All three end in $91$, all three carry the fingerprint of class $91$.

This paper studies the forty collision values. It shows what they look like in base $10$, names the symmetry that holds them together, and explains the structural bias built into the table.

## Forty integers in base ten

Here is the table, computed from [nfield](https://github.com/alexspetty/nfield) for every coprime class modulo $100$. The row is the tens digit of the class. The column is the units digit. A dot marks the classes that are not coprime to $10$ (the rows ending in even digits, and the column $5$).

```
       0    1    2    3    4    5    6    7    8    9
  0    .   +0    .   +2    .    .    .   +0    .   +8
 10    .   -1    .   -1    .    .    .   +1    .   -1
 20    .   +0    .   -2    .    .    .   +6    .   +0
 30    .   -1    .   -1    .    .    .   -3    .   -1
 40    .   -4    .   +0    .    .    .   -2    .   +0
 50    .   -1    .   +1    .    .    .   -1    .   +3
 60    .   +0    .   +2    .    .    .   +0    .   +0
 70    .   -1    .   -7    .    .    .   +1    .   -1
 80    .   +0    .   -2    .    .    .   +0    .   +0
 90    .   -9    .   -1    .    .    .   -3    .   -1
```

Forty entries, all integers, all small. Eight of them are positive, twelve are zero, twenty are negative. The largest is $+8$ at class $09$. The smallest is $-9$ at class $91$. These two extremes will turn out to be paired with each other, but that is a story for the next section.

The integer attached to class $a$ is what I call the *collision fingerprint* of any prime ending in $a$. It is computed by counting how many residues mod $p$ share their digit bin with the residue's image under multiplication by the base, then subtracting a simple correction. The result is a small signed integer that, at lag $1$, depends only on $p \bmod 100$.

That is the table. Every prime past one hundred gets assigned one of these forty integers, by the simplest fact about the prime that you can name.

When I describe the alignment program to anyone, this is the picture I show. The forty cells are concrete enough that a numerate reader can verify the antisymmetry I am about to walk through by adding entries on a finger, and rigid enough that the later analytic work had no choice but to reckon with them. In 2023, though, the point was simpler: the table itself already looked like structure, not noise.

![The collision periodic table in base 10](https://alexpetty.com/content/images/2026/04/collision_periodic_table_heatmap-1.png)

## The pattern in the pairs

Look at the table again. This time, pair off the classes by complement. Class $a$ and class $100 - a$. So $9$ goes with $91$, $1$ with $99$, $3$ with $97$, $7$ with $93$, and so on. Twenty pairs total. Read the values in each pair and add them.

```
class    a     S(a)    100 - a    S(100 - a)    sum
-----  ----   -----    -------    ----------    ---
   9    +8        91         -9                  -1
   1    +0        99         -1                  -1
   3    +2        97         -3                  -1
   7    +0        93         -1                  -1
  11    -1        89         +0                  -1
  13    -1        87         +0                  -1
  17    +1        83         -2                  -1
  19    -1        81         +0                  -1
  21    +0        79         -1                  -1
  23    -2        77         +1                  -1
  27    +6        73         -7                  -1
  29    +0        71         -1                  -1
  31    -1        69         +0                  -1
  33    -1        67         +0                  -1
  37    -3        63         +2                  -1
  39    -1        61         +0                  -1
  41    -4        59         +3                  -1
  43    +0        57         -1                  -1
  47    -2        53         +1                  -1
  49    +0        51         -1                  -1
```

Every single pair sums to exactly $-1$. Twenty pairs, twenty negative ones. Not a single exception, not a single approximation.

That is the antisymmetry of the table, and it is sharp. $S(a) + S(100 - a) = -1$ at every coprime class $a$ in base ten, and the same equation holds in every other base, with the same constant $-1$ on the right. The proof in the paper takes three lines of bookkeeping: a complementary count over a single sum, a floor-arithmetic identity, and an assembly step. Out falls $-1$.

The reason the constant is $-1$ rather than $0$ is also clean. The collision count $C$ excludes the residue zero, and the complement map $r \mapsto p - r$ that sends digit $d$ to digit $b - 1 - d$ has a parity offset that lands at exactly $-1$. The structure forces it.

![Every pair on the line](https://alexpetty.com/content/images/2026/04/periodic_table_pairs.png)

I want to call out what this antisymmetry does to the table, because it is more than a curiosity. The mean of the forty integers is the average of $-1$ across $20$ pairs, divided by the $40$ classes. That gives exactly $-1/2$. Not $-0.5001$, not $-0.4998$, exactly $-1/2$.

It also forces a *structural negative bias*. If every pair sums to $-1$, and at least one member of each pair must therefore be negative, then exactly half of the forty classes are negative. This is not a sampling artifact that washes out at large $b$. It is a forced consequence of the pair sum, and it survives into every later paper in the program that uses the centered collision deviations as a signal. I cannot stress enough how much trouble it would have caused if this bias had been a statistical fluctuation instead of a theorem. The bias is the table's signature, baked into the structure from the moment the antisymmetry is proved.

## Every base does the same thing

The forty-cell table in base $10$ is one instance of a pattern that holds in every base. Here is what nfield computes for the first few bases past trivial:

```
 b   φ(b²)   range S      +    0    -     antisymmetry constant
 -   -----   --------    --   --   --    ---------------------
 3      6    [-2, +1]     1    2    3            -1
 5     20    [-4, +3]     4    6   10            -1
 6     12    [-5, +4]     2    4    6            -1
 7     42    [-6, +5]    10   11   21            -1
 8     32    [-7, +6]     7    9   16            -1
10     40    [-9, +8]     8   12   20            -1
12     48   [-11,+10]    11   13   24            -1
```

Same shape every time. The range is exactly $[-(b - 1), b - 2]$, achieved at the classes $a = b - 1$ (which gives $S = b - 2$) and $a = b^2 - b + 1$ (which gives $S = -(b - 1)$). The pair sum is exactly $-1$ no matter the base. The negative classes always outnumber the positive, because every pair contains at least one negative member, and the pairs containing zero count it on only one side.

Every base produces its own table, with $\varphi(b^2)$ cells in general, and every one of those tables has the same structural fingerprint. The base picks the size and the specific values. The structure does not move.

## The table as starting point

I am calling this object "the collision periodic table" because the name fits. The chemical periodic table organizes a finite collection of elements by an internal symmetry, and what falls out is a predictive structure for chemistry. The collision table organizes a finite collection of integers by the antisymmetric pair structure, and I suspect that what falls out will be a predictive structure for something deeper. I do not yet know what. But forty integers, all small, all forced by one symmetry, all determined by the last two digits of a prime, has the character of a foundation.

The table is where the centered collision sum gets its data. The convergence at $s = 1$ that [the centered collision sum](https://alexpetty.com/the-centered-collision-sum/) proved is a statement about these forty integers, summed over primes. Whatever the collision invariant turns out to encode about primes, it will have to read these forty integers as its input.

.:.
## A note from 2026

*April 2026*

The table turned out to encode far more than I understood when I first computed it.

Two years after this paper, the decomposition theorem from [the collision spectrum](https://alexpetty.com/the-collision-spectrum-and-the-l-function-landscape/) showed that the Fourier coefficients of the table factor through Bernoulli numbers and diagonal character sums. That later factorization revealed a surprise hiding in the forty integers.

Take the table. Run a Fourier transform on it. Of the forty characters, only eight carry nonzero coefficients, the primitive odd characters mod $100$. In the later spectrum papers, those coefficients become tied to Bernoulli data and therefore to $L(1,\chi)$ values. What looked in 2023 like a finite combinatorial table became, in 2026, part of an analytic encoding story.

The forty integers are the elementary side of that later identity. The table I wrote down in 2023 as a structural curiosity turned out to sit at the front of the Fourier/Bernoulli machinery that came much later.

The collision periodic table became the elementary anchor for every analytic result in the program. The [anti-correlation](https://alexpetty.com/the-general-neutrality-theorem/), the [spectral repulsion](https://alexpetty.com/the-spectral-repulsion/), and the [L-value encoding](https://alexpetty.com/the-collision-spectrum-and-the-l-function-landscape/) all run on this table as input. The connection to class numbers was the deepest surprise. For imaginary quadratic fields, $h(-d) = (\sqrt{d}/\pi) |L(1, \chi_d)|$. At base $5$, the collision coefficient is proportional to $h(-d)^2$. The digit function squares class numbers.

.:.

---

## Try it yourself

Print the collision periodic table. Forty integers, determined by the last two digits of every prime past $100$.

```
$ ./nfield collision_table 10
```

Check the antisymmetry. Pair off class $a$ with class $100 - a$. Every pair should sum to exactly $-1$. Twenty pairs, twenty negative ones.

```
$ ./nfield collision_table 10 --pairs
```

Try a different base. The range, the antisymmetry constant, and the negative bias should all hold. Only the specific integers change.

```
$ ./nfield collision_table 7
```

Code: [github.com/alexspetty/nfield](https://github.com/alexspetty/nfield)
Paper: [The Collision Periodic Table](https://github.com/alexspetty/nfield/blob/main/research/collision_periodic_table.pdf)

---

*Alexander S. Petty*
December 2023 (updated April 2026)
.:.
