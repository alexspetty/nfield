#!/usr/bin/env python3
"""
Prism: decompose the correlation signal by bin.

For each composite digit d, compute the correlation
function restricted to collisions landing in bin d.

X_d(r, g) = 1 if floor(br/n) = d AND floor(bgr/n) = d.

The ghost collisions cluster at specific bins (the ones
where the interleaving function f has column collisions).
Restricting to those bins should amplify the factor signal.
"""
import math

b = 10
p, q = 7, 13
n = p * q

def collision_bin(r, g, n, b):
    """Return the bin if collision, else -1."""
    d1 = b * r // n
    gr = g * r % n
    d2 = b * gr // n
    if d1 == d2:
        return d1
    return -1

# For each bin d, compute correlation by distance
print(f"n = {n} = {p} x {q}, base {b}\n")

for d in range(b):
    # Count residues in this bin
    bin_size = sum(1 for r in range(1, n) if b * r // n == d and math.gcd(r, n) == 1)

    both_by_mod = {}
    one_by_mod = {}

    for dist in range(2, n):
        if math.gcd(dist, n) != 1:
            continue

        both = 0
        one = 0

        for r in range(1, n):
            if math.gcd(r, n) != 1:
                continue
            if b * r // n != d:
                continue

            for g in range(2, n):
                if math.gcd(g, n) != 1:
                    continue
                gd_mult = g * dist % n
                if math.gcd(gd_mult, n) != 1:
                    continue

                # Collision at g in bin d?
                c1 = collision_bin(r, g, n, b)
                c2 = collision_bin(r, gd_mult, n, b)

                if c1 == d:
                    one += 1
                    if c2 == d:
                        both += 1

        for m in [7, 13]:
            k = dist % m
            key = (m, k)
            both_by_mod[key] = both_by_mod.get(key, 0) + both
            one_by_mod[key] = one_by_mod.get(key, 0) + one

    # Report for this bin
    print(f"Bin {d} ({bin_size} residues):")
    for m in [7, 13]:
        excess_1 = None
        vals = []
        for k in range(m):
            key = (m, k)
            b_tot = both_by_mod.get(key, 0)
            o_tot = one_by_mod.get(key, 0)
            cp = b_tot / o_tot if o_tot > 0 else -1
            vals.append(cp)
            if k == 1:
                excess_1 = cp

        valid = [v for v in vals if v >= 0]
        if valid:
            mean = sum(valid) / len(valid)
            exc = excess_1 - mean if excess_1 >= 0 else 0
            print(f"  mod {m:>2}: d≡1 = {excess_1:.4f}, "
                  f"mean = {mean:.4f}, "
                  f"excess = {exc:+.4f}")
    print()
