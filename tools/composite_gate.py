#!/usr/bin/env python3
"""
composite_gate.py: Does the gate width theorem extend to composites?

Paper 11 proves: every prime p (with gcd(p,b)=1) has exactly b-1
deranging multipliers g where C(g) = 0.

Question: does every composite n (with gcd(n,b)=1) also have
exactly b-1 deranging multipliers?

And: can we decompose C_n(g) in terms of the factors' collision
structure plus a deterministic correction?
"""

from collections import defaultdict
import math

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def collision_count(n, g, base=10):
    if g % n == 0:
        return 0
    count = 0
    for r in range(1, n):
        gr = (g * r) % n
        if gr == 0:
            continue
        if (base * r) // n == (base * gr) // n:
            count += 1
    return count

def deranging_set(n, base=10):
    deranging = []
    for g in range(2, n):
        if gcd(g, n) != 1:
            continue
        if collision_count(n, g, base) == 0:
            deranging.append(g)
    return deranging

def mult_order(base, n):
    if gcd(base, n) != 1:
        return 0
    r = 1
    for k in range(1, n + 1):
        r = (r * base) % n
        if r == 1:
            return k
    return 0

def euler_phi(n):
    result = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result

def analyze_gate_width(base=10):
    print(f"GATE WIDTH AT COMPOSITES (base {base})")
    print(f"Expected deranging count for primes: {base - 1}")
    print()
    print(f"  {'n':>5s} {'type':>10s} {'phi(n)':>6s} {'ord':>5s} "
          f"{'#derang':>7s} {'b-1?':>5s} {'deranging set':>30s}")
    print(f"  {'-'*75}")

    for n in range(4, 200):
        if gcd(n, base) != 1:
            continue

        # Classify
        temp = n
        factors = []
        d = 2
        while d * d <= temp:
            while temp % d == 0:
                factors.append(d)
                temp //= d
            d += 1
        if temp > 1:
            factors.append(temp)

        if len(factors) == 1:
            ntype = "prime"
        elif len(set(factors)) == 1:
            ntype = f"{factors[0]}^{len(factors)}"
        else:
            ntype = "x".join(str(f) for f in factors)

        if len(factors) < 2:
            continue  # skip primes, we know they work

        ds = deranging_set(n, base)
        count = len(ds)
        matches = "YES" if count == base - 1 else "NO"

        ds_str = str(ds) if len(ds) <= 10 else str(ds[:8]) + "..."

        print(f"  {n:5d} {ntype:>10s} {euler_phi(n):6d} "
              f"{mult_order(base, n):5d} {count:7d} {matches:>5s} "
              f"{ds_str:>30s}")

    # Also test some specific semiprimes
    print(f"\n  Specific semiprimes:")
    semiprimes = [(7,11), (7,13), (11,13), (13,17), (29,31),
                  (37,41), (7,41), (11,29), (3,7), (3,11), (3,13)]
    for p, q in semiprimes:
        n = p * q
        if gcd(n, base) != 1:
            continue
        ds = deranging_set(n, base)
        ds_p = deranging_set(p, base)
        ds_q = deranging_set(q, base)

        # Check overlap between composite and factor deranging sets
        # Map factor deranging to composite via CRT
        overlap_p = [g for g in ds if g % p in set(ds_p) | {0}]
        overlap_q = [g for g in ds if g % q in set(ds_q) | {0}]

        print(f"\n  n={n} = {p}x{q}:")
        print(f"    Deranging at {p}: {ds_p}")
        print(f"    Deranging at {q}: {ds_q}")
        print(f"    Deranging at {n}: {ds}  (count={len(ds)})")
        print(f"    g mod {p} for composite deranging: "
              f"{[g % p for g in ds]}")
        print(f"    g mod {q} for composite deranging: "
              f"{[g % q for g in ds]}")

        # Key test: is the composite deranging set determined by
        # the factor deranging sets via CRT?
        # If g is deranging at n, is g mod p deranging at p
        # AND g mod q deranging at q?
        both_deranging = all(
            (g % p in ds_p or g % p == 0) and
            (g % q in ds_q or g % q == 0)
            for g in ds
        )
        either_deranging = all(
            (g % p in ds_p or g % p == 0) or
            (g % q in ds_q or g % q == 0)
            for g in ds
        )
        print(f"    All composite deranging are deranging at BOTH factors: "
              f"{both_deranging}")
        print(f"    All composite deranging are deranging at EITHER factor: "
              f"{either_deranging}")

    # Collision count decomposition
    print(f"\n\n  COLLISION DECOMPOSITION TEST")
    print(f"  For n=pq, is C_n(g) determined by C_p(g mod p), C_q(g mod q)?")

    for p, q in [(7, 11), (13, 17), (29, 31)]:
        n = p * q
        print(f"\n  n={n} = {p}x{q}:")
        print(f"  {'g':>5s} {'g%p':>5s} {'g%q':>5s} "
              f"{'C_n':>5s} {'C_p':>5s} {'C_q':>5s} "
              f"{'C_p*C_q':>7s} {'diff':>6s} {'ratio':>7s}")

        for g in range(2, min(n, 50)):
            if gcd(g, n) != 1:
                continue
            gp = g % p
            gq = g % q
            cn = collision_count(n, g, base)
            cp = collision_count(p, gp, base) if gp != 0 else 0
            cq = collision_count(q, gq, base) if gq != 0 else 0
            product = cp * cq
            diff = cn - product
            ratio = cn / product if product > 0 else float('inf')
            print(f"  {g:5d} {gp:5d} {gq:5d} "
                  f"{cn:5d} {cp:5d} {cq:5d} "
                  f"{product:7d} {diff:+6d} {ratio:7.3f}")


if __name__ == '__main__':
    analyze_gate_width()
