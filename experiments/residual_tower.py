#!/usr/bin/env python3
"""
Is the residual at lag ell the stamp at lag ell+1?

If S°(lag 1) correlates with the ADDITIONAL digit of p
(i.e., p mod b^3 vs p mod b^2), then the lag-1 residual
is captured by the lag-2 stamp. The tower has no secrets.
"""

from math import gcd

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def collision_count(g, p, b):
    count = 0
    for r in range(1, p):
        if b * r // p == b * (g * r % p) // p:
            count += 1
    return count

def test_tower(b, max_p):
    m1 = b * b        # lag 1 modulus
    m2 = b * b * b    # lag 2 modulus

    print(f"\n{'='*60}")
    print(f"BASE {b}: lag 1 mod {m1}, lag 2 mod {m2}")
    print(f"{'='*60}")

    # Compute S at lag 1 for all primes
    # Group by p mod m1 (lag 1 stamp) AND p mod m2 (lag 2 stamp)
    data = {}  # key: (p mod m1, p mod m2), value: list of S values

    for p in range(m2 + 1, max_p):
        if not is_prime(p) or p % b == 0:
            continue
        g = pow(b, 1, p)
        C = collision_count(g, p, b)
        Q = (p - 1) // b
        S = C - Q

        key1 = p % m1
        key2 = p % m2

        if (key1, key2) not in data:
            data[(key1, key2)] = []
        data[(key1, key2)].append(S)

    # For each lag-1 class, check if S° varies with the lag-2 sub-class
    # First compute lag-1 class means
    lag1_vals = {}
    for (k1, k2), svals in data.items():
        if k1 not in lag1_vals:
            lag1_vals[k1] = []
        lag1_vals[k1].extend(svals)

    lag1_mean = {k: sum(v)/len(v) for k, v in lag1_vals.items()}

    # Now for each lag-1 class, look at the sub-classes (lag-2)
    print(f"\nDoes the lag-1 residual depend on p mod {m2}?")
    print(f"(i.e., is the residual at lag 1 = stamp at lag 2?)\n")

    # Pick a few lag-1 classes to examine
    example_classes = sorted(lag1_vals.keys())[:6]

    for k1 in example_classes:
        if gcd(k1, b) != 1 and k1 != 1:
            continue

        # Find all lag-2 sub-classes within this lag-1 class
        sub = {}
        for (kk1, k2), svals in data.items():
            if kk1 != k1:
                continue
            sub[k2] = sum(svals) / len(svals)

        if len(sub) < 2:
            continue

        # Compute residuals: sub-class mean minus lag-1 mean
        residuals = {k2: sub[k2] - lag1_mean[k1] for k2 in sorted(sub.keys())}

        # Check if residuals vary (if they're all ~0, lag 2 adds nothing)
        res_vals = list(residuals.values())
        spread = max(res_vals) - min(res_vals)

        print(f"  p mod {m1} = {k1}: lag-1 mean = {lag1_mean[k1]:+.4f}")
        print(f"    sub-classes mod {m2}:")
        for k2 in sorted(sub.keys())[:8]:
            n_primes = len(data.get((k1, k2), []))
            print(f"      p mod {m2} = {k2:>4}: mean S = {sub[k2]:+.4f}  "
                  f"residual = {residuals[k2]:+.4f}  (n={n_primes})")
        if len(sub) > 8:
            print(f"      ... ({len(sub)} sub-classes total)")
        print(f"    Spread of residuals: {spread:.4f}")
        print(f"    {'RESIDUAL HAS STRUCTURE' if spread > 0.5 else 'RESIDUAL IS FLAT (noise)'}")
        print()

test_tower(3, 20000)
test_tower(5, 20000)
