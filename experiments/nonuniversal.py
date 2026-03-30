#!/usr/bin/env python3
"""
Non-universal test: do C(g1) and C(g2) differ when
g1 ≡ g2 mod b^2 but g1 ≢ g2 mod n?

At primes: C depends on g mod b^2, so C(g1) = C(g2).
At composites: C depends on g mod n (Transform 2),
so C(g1) might ≠ C(g2).

The difference C(g1) - C(g2) is a NON-UNIVERSAL signal:
zero at primes, potentially nonzero at composites.

Cost: O(n) per collision count. Two counts = O(n).
But you only need TWO evaluations, not phi(n).
"""
import math

b = 10
m = b * b  # 100

def C(n, g):
    """Collision count at modulus n, multiplier g."""
    count = 0
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        if b * r // n == b * (g * r % n) // n:
            count += 1
    return count

# Test at composite n = 91 = 7 x 13
n = 91
print(f"n = {n} = 7 x 13\n")

# Find pairs g1, g2 with g1 ≡ g2 mod 100, g1 ≢ g2 mod 91
print(f"Pairs g1 ≡ g2 mod {m}, g1 ≢ g2 mod {n}:")
print(f"{'g1':>4} {'g2':>4} {'g1%100':>6} {'g2%100':>6} {'C(g1)':>6} {'C(g2)':>6} {'diff':>5}")

found = 0
for g1 in range(2, n):
    if math.gcd(g1, n) != 1:
        continue
    for g2 in range(g1 + 1, min(g1 + 300, 500)):
        if math.gcd(g2, n) != 1:
            continue
        if g1 % m == g2 % m and g1 % n != g2 % n:
            c1 = C(n, g1)
            c2 = C(n, g2)
            diff = c1 - c2
            if found < 15:
                print(f"{g1:4d} {g2:4d} {g1%m:6d} {g2%m:6d} {c1:6d} {c2:6d} {diff:>5d}")
            found += 1

print(f"\nTotal pairs found: {found}")

# Now same test at a prime p = 97
print(f"\n\n=== Prime p = 97 ===")
n2 = 97
found2 = 0
diffs_prime = []
for g1 in range(2, n2):
    if math.gcd(g1, n2) != 1:
        continue
    for g2 in range(g1 + 1, min(g1 + 300, 500)):
        if math.gcd(g2, n2) != 1:
            continue
        if g1 % m == g2 % m and g1 % n2 != g2 % n2:
            c1 = C(n2, g1)
            c2 = C(n2, g2)
            diff = c1 - c2
            diffs_prime.append(diff)
            if found2 < 10:
                print(f"g1={g1}, g2={g2}: C(g1)={c1}, C(g2)={c2}, diff={diff}")
            found2 += 1

print(f"Total pairs: {found2}")
if diffs_prime:
    nonzero = sum(1 for d in diffs_prime if d != 0)
    print(f"Nonzero diffs: {nonzero} / {len(diffs_prime)}")
