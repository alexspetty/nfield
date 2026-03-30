#!/usr/bin/env python3
"""
Reformulate the wrapping condition as a lattice point problem.

The wrapping set W = {a : ca mod m < a} can be rewritten as:
  ca mod m < a
  ca - m*floor(ca/m) < a
  floor(ca/m) > (ca - a)/m = a(c-1)/m

So a is in W iff floor(ca/m) > a(c-1)/m.

Since floor(x) > y iff floor(x) >= ceil(y+epsilon),
this is: floor(ca/m) >= floor(a(c-1)/m) + 1
which is: floor(ca/m) - floor(a(c-1)/m) >= 1
which is: floor(ca/m) > floor((c-1)a/m)

This means: the integer part of ca/m is strictly greater
than the integer part of (c-1)a/m. In other words, there
is an integer in the interval ((c-1)a/m, ca/m].

The interval has length a/m. So the condition is:
"the interval ((c-1)a/m, ca/m] contains an integer."

An interval of length a/m contains an integer iff
{(c-1)a/m} > 1 - a/m, i.e., {(c-1)a/m} + a/m > 1.

So: a in W iff {(c-1)a/m} > 1 - a/m.

Let's verify this and see what it means geometrically.
"""

from math import gcd, floor

def check_reformulation(b):
    m = b * b
    units = [a for a in range(1, m) if gcd(a, m) == 1]
    G = [n for n in range(m) if n // b == n % b]

    print(f"Base {b}, m={m}")

    for n in G:
        c = n + 1
        if c % m == 0 or c == 1: continue

        # Original wrapping set
        W_orig = set(a for a in units if (c * a % m) < a)

        # Reformulation 1: floor(ca/m) > floor((c-1)a/m)
        W_floor = set(a for a in units
                      if floor(c * a / m) > floor((c-1) * a / m))

        # Reformulation 2: {(c-1)a/m} > 1 - a/m
        W_frac = set(a for a in units
                     if ((c-1) * a % m) / m > 1 - a/m)

        match1 = W_orig == W_floor
        match2 = W_orig == W_frac

        print(f"  n={n}, c={c}: floor reform={match1}, frac reform={match2}")

        if match2:
            # Show the condition: {(c-1)a/m} > 1 - a/m
            # This is: {(c-1)a/m} + {a/m} > 1
            # Which is: the sum of two fractional parts exceeds 1
            # This happens iff the addition "wraps"
            print(f"    Condition: {{(c-1)a/m}} + a/m > 1")
            print(f"    = fractional part of (c-1)a/m plus a/m exceeds 1")
            print(f"    = adding a/m to {{(c-1)a/m}} causes a carry")

        break  # first slice only

check_reformulation(3)
check_reformulation(5)
check_reformulation(7)

print("\n" + "="*60)
print("THE REFORMULATION")
print("="*60)
print("""
a is in the wrapping set W iff:

  {(c-1)a/m} + a/m > 1

This is the "carry condition": when you add a/m to the
fractional part of (c-1)a/m, the sum exceeds 1.

Equivalently: there is an integer in the half-open
interval ((c-1)a/m, ca/m].

This is a LATTICE POINT condition. We are counting
lattice points (integers) in intervals of length a/m
centered at positions (c-1/2)a/m.

The character sum over W is therefore:

  sum_{a in W} chi(a) = sum_a chi(a) * 1_{carry at a}

where the carry indicator depends on {(c-1)a/m}.

The fractional parts {(c-1)a/m} for a ranging over
units mod m are equidistributed (by Weyl's theorem,
since c-1 is coprime to m for good slices).

So the carry happens when {(c-1)a/m} > 1 - a/m.
Since a/m ranges from 1/m to (m-1)/m, the threshold
varies with a. But the fractional parts are equidistributed.

The character sum is:
  sum_a chi(a) * 1_{{(c-1)a/m} > 1 - a/m}

This is an INCOMPLETE character sum with a variable
threshold. Van der Corput / exponential sum methods
apply to exactly this type of sum.
""")
