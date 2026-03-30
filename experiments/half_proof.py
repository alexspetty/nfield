#!/usr/bin/env python3
"""
Why is the wrapping set always exactly half the units?

Wrapping set for good slice n: W_n = {a : (n+1)a mod m < a}
where m = b^2, a coprime to m.

Claim: |W_n| = phi(m)/2 for every non-trivial good slice.

Let's understand WHY. The condition (n+1)a mod m < a is:
  {(n+1)a/m} < a/m  (since a < m, a/m = {a/m})

So: the fractional part of (n+1)a/m is less than a/m.

Equivalently: multiplication by (n+1) DECREASES the
fractional part of a/m.

For c = n+1, this is: {ca/m} < {a/m}.

Now, {ca/m} = {a/m + (c-1)a/m} = {{a/m} + {(c-1)a/m} + ...}
Not quite -- need to think about this more carefully.

Actually: ca/m = a/m + (c-1)a/m. So {ca/m} < {a/m} iff
the addition of (c-1)a/m to a/m causes a "wrap" past an
integer. That happens iff floor(ca/m) > floor(a/m) + floor((c-1)a/m).

Hmm, simpler: {ca/m} < {a/m} iff ca mod m < a (since a < m).
And ca mod m < a iff ca - floor(ca/m)*m < a iff
floor(ca/m) > (ca - a)/m = a(c-1)/m.

So the condition is: floor(ca/m) > a(c-1)/m.
Since floor(x) > y iff floor(x) >= floor(y) + 1 when y is
not an integer... this is getting complicated.

Let's try a different angle. For fixed c coprime to m,
the map a -> ca mod m is a permutation of the units.
The condition ca mod m < a partitions the units into two sets:
  W = {a : ca mod m < a}
  W' = {a : ca mod m >= a}

Claim: |W| = |W'| = phi(m)/2.

This would follow if the map a -> ca mod m is an
INVOLUTION-FREE permutation that pairs each a with ca in
a way that exactly one of {a, ca} is in W.

But ca mod m is not generally an involution.

Alternative: consider the map a -> m - a. This is an
involution on the units (when m is odd or a is coprime).
Does it swap W and W'?

If a is in W: ca mod m < a.
Is m-a in W'? We need c(m-a) mod m >= m-a.
c(m-a) mod m = (cm - ca) mod m = (-ca) mod m = m - (ca mod m).
So: m - (ca mod m) >= m - a iff ca mod m <= a.
That's ca mod m <= a, which is W union {a : ca mod m = a}.

So a in W (ca mod m < a) implies m-a has
c(m-a) mod m = m - ca mod m > m - a - 1...

Let me just check: does a -> m-a swap W and W'?
"""

from math import gcd

def check_involution_swap(b):
    m = b * b
    units = [a for a in range(1, m) if gcd(a, m) == 1]

    # Good slices
    G = [n for n in range(m) if n // b == n % b]

    print(f"Base {b}, m={m}")

    for n in G:
        c = n + 1
        if c % m == 0 or c == 1:
            continue

        W = set(a for a in units if (c * a % m) < a)
        W_comp = set(a for a in units if (c * a % m) >= a)

        # Check: does a -> m-a swap W and W_comp?
        swaps = 0
        stays = 0
        for a in W:
            ma = m - a
            if ma in W_comp:
                swaps += 1
            elif ma in W:
                stays += 1

        # Also check: does a -> ca mod m pair W with W_comp?
        pairs_cross = 0
        pairs_same = 0
        for a in units:
            ca = c * a % m
            if (a in W and ca in W_comp) or (a in W_comp and ca in W):
                pairs_cross += 1
            else:
                pairs_same += 1

        print(f"  n={n}, c={c}: |W|={len(W)}, |W'|={len(W_comp)}")
        print(f"    a->m-a swaps W<->W': {swaps}/{len(W)}")
        print(f"    a->ca crosses W<->W': {pairs_cross}/{len(units)}")

check_involution_swap(3)
check_involution_swap(5)
check_involution_swap(7)
