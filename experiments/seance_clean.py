#!/usr/bin/env python3
"""
Clean seance: exclude d=1 and small distances to remove
the identity contamination. Look for factor-specific dips
or peaks in the correlation function.
"""
import math, random

b = 10
p, q = 7, 13
n = p * q

def modinv(a, m):
    g, x = 0, 1
    a0, m0 = a % m, m
    while a0 != 0:
        qq = m0 // a0
        m0, a0 = a0, m0 - qq * a0
        g, x = x, g - qq * x
    return g % m

def collision_check(r, g, n, b):
    gr = g * r % n
    return b * r // n == b * gr // n

# Exhaustive computation for clarity (small n)
# For each distance d > 1, compute the exact conditional probability
print(f"n = {n} = {p} x {q}")
print(f"\nExact correlation, d > 5:")

corr_by_mod = {}  # {m: {k: (both, one)}}

for d in range(2, n):
    if math.gcd(d, n) != 1:
        continue

    both = 0
    one = 0
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        for g in range(2, n):
            if math.gcd(g, n) != 1:
                continue
            gd = g * d % n
            if math.gcd(gd, n) != 1:
                continue
            x1 = collision_check(r, g, n, b)
            x2 = collision_check(r, gd, n, b)
            if x1:
                one += 1
                if x2:
                    both += 1

    cp = both / one if one > 0 else 0

    for m in [7, 13, 5, 11, 17]:
        if m not in corr_by_mod:
            corr_by_mod[m] = {}
        k = d % m
        if k not in corr_by_mod[m]:
            corr_by_mod[m][k] = [0, 0]
        corr_by_mod[m][k][0] += both
        corr_by_mod[m][k][1] += one

# Report
for m in [7, 13, 5, 11, 17]:
    is_factor = (n % m == 0)
    print(f"\nCorrelation by d mod {m} {'(FACTOR)' if is_factor else ''}:")
    vals = []
    for k in range(m):
        b_tot, o_tot = corr_by_mod[m].get(k, [0, 1])
        cp = b_tot / o_tot if o_tot > 0 else 0
        vals.append(cp)
        bar = "#" * int(cp * 200)
        marker = " <-- d≡1" if k == 1 else ""
        print(f"  d≡{k:>2}: {cp:.6f}  {bar}{marker}")

    mean = sum(vals) / len(vals)
    peak = vals[1]
    print(f"  mean={mean:.6f}, d≡1={peak:.6f}, excess={peak-mean:.6f}")
