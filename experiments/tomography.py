#!/usr/bin/env python3
"""
Collision tomography.

The digit function floor(br/n) projects the CRT grid onto b bins.
Each base b gives a different projection angle. Multiple bases
give multiple projections. Can we reconstruct the grid (= factor n)?

KEY INSIGHT: At base b = p, floor(pr/pq) = floor(r/q).
The digit function becomes the q-binning. The p-structure
becomes invisible and the q-structure becomes fully visible.

So if we sweep bases and DETECT when the projection aligns
with a factor, we factor n.

What does "alignment with a factor" look like in the collision
invariant?
"""
import math

def collision_count(n, base, g):
    """C(g) at modulus n in given base."""
    count = 0
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        if base * r // n == base * (g * r % n) // n:
            count += 1
    return count

def mean_collision(n, base):
    """Mean C(g) across all coprime g."""
    total = 0
    count = 0
    for g in range(2, min(n, 50)):
        if math.gcd(g, n) != 1:
            continue
        total += collision_count(n, base, g)
        count += 1
    return total / count if count > 0 else 0

n = 91  # 7 * 13

print(f"n = {n} = 7 x 13")
print(f"Sweeping bases b = 2..20")
print(f"{'base':>5} {'mean_C':>8} {'Q':>4} {'mean_C/Q':>9} {'note':>15}")

for base in range(2, 21):
    if math.gcd(base, n) != 1:
        print(f"{base:5d} {'---':>8} {'':>4} {'':>9} {'shares factor':>15}")
        continue
    Q = (n - 1) // base
    mc = mean_collision(n, base)
    ratio = mc / Q if Q > 0 else 0

    note = ""
    if base == 7:
        note = "<-- b = p"
    elif base == 13:
        note = "<-- b = q"
    elif base == 14:
        note = "<-- b = 2p"

    print(f"{base:5d} {mc:8.2f} {Q:4d} {ratio:9.4f} {note:>15}")

# Now look at it differently: at base b, the number of
# DERANGING multipliers is always b-1 (gate width).
# But the SPECIFIC deranging set changes with base.
# At b = p, the deranging condition c = p(1-g)^{-1} mod n
# simplifies because the base IS a factor of n.

print(f"\nDeranging sets at key bases:")
for base in [5, 6, 7, 8, 10, 12, 13, 14, 15]:
    if math.gcd(base, n) != 1:
        print(f"  base {base}: shares factor with n")
        continue
    D = []
    for g in range(2, n):
        if math.gcd(g, n) != 1:
            continue
        C = collision_count(n, base, g)
        if C == 0:
            D.append(g)
    print(f"  base {base}: {len(D)} deranging (expected {base-1})")
