#!/usr/bin/env python3
"""
The deranging set at n = pq contains g's where g ≡ 1 mod p
or g ≡ 1 mod q (when the other factor is DP).

These "factor-aligned" deranging multipliers have a special
structure: they form arithmetic progressions mod p or mod q.

If we can identify these progressions in the deranging set,
we can recover p and q.

The deranging set has exactly b-1 elements (gate width).
Among these, some satisfy the c-criterion (c in {1,...,b-1})
and some are "extra" (gcd(1-g, n) > 1).

The "extra" ones satisfy g ≡ 1 mod p or g ≡ 1 mod q.
So gcd(g-1, n) reveals a factor!

LET'S CHECK.
"""
import math

b = 10

def deranging_set_direct(n, b):
    deranging = []
    for g in range(2, n):
        if math.gcd(g, n) != 1:
            continue
        C = 0
        for r in range(1, n):
            if math.gcd(r, n) != 1:
                continue
            if b * r // n == b * (g * r % n) // n:
                C += 1
                break  # one collision suffices to prove non-deranging
        if C == 0:
            deranging.append(g)
    return deranging

composites = [
    (7, 13),
    (7, 11),
    (11, 13),
    (7, 17),
    (13, 17),
    (7, 19),
    (11, 19),
    (13, 23),
]

for p, q in composites:
    n = p * q
    D = deranging_set_direct(n, b)

    print(f"n = {p} x {q} = {n}, deranging set ({len(D)} elements):")

    factors_found = set()
    for g in D:
        d = math.gcd(g - 1, n)
        if d > 1 and d < n:
            factors_found.add(d)
            print(f"  g={g:>4}: gcd(g-1, n) = {d}  ** FACTOR **")

    if factors_found:
        print(f"  FACTORS FOUND: {sorted(factors_found)}")
    else:
        print(f"  No factors from gcd(g-1, n)")
    print()
