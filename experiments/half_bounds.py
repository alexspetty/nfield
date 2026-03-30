#!/usr/bin/env python3
"""
How do the wrapping half-sums compare to known bounds?

Polya-Vinogradov: |sum chi(a)| <= sqrt(m) * log(m) for any half
Our half-sums: what are the actual magnitudes?
Generic random half: expected magnitude ~ sqrt(phi(m)/2)
"""
import cmath
from math import gcd, pi, sqrt, log

def primitive_root(n):
    phi = n
    temp = n; p = 2; factors = []
    while p * p <= temp:
        if temp % p == 0:
            factors.append(p)
            while temp % p == 0: temp //= p
        p += 1
    if temp > 1: factors.append(temp)
    for f in factors: phi = phi - phi // f
    for g in range(2, n):
        if gcd(g, n) != 1: continue
        ok = True
        for f in factors:
            if pow(g, phi // f, n) == 1: ok = False; break
        if ok: return g, phi
    return None, phi

for b in [3, 5, 7, 11, 13]:
    m = b * b
    gen, phi = primitive_root(m)
    if gen is None: continue

    units = [a for a in range(1, m) if gcd(a, m) == 1]
    dlog = {}; pw = 1
    for k in range(phi): dlog[pw] = k; pw = (pw * gen) % m

    omega = cmath.exp(2j * pi / phi)
    G = [n for n in range(m) if n // b == n % b]

    # Bounds
    pv_bound = sqrt(m) * log(m)  # Polya-Vinogradov
    random_bound = sqrt(phi / 2)  # random half expectation
    half_size = phi // 2

    print(f"Base {b}, m={m}, phi={phi}")
    print(f"  Polya-Vinogradov bound: {pv_bound:.2f}")
    print(f"  Random half expected:   {random_bound:.2f}")
    print(f"  Half size:              {half_size}")

    # Compute actual half-sums for first non-trivial good slice
    for n in G:
        c = n + 1
        if c % m == 0 or c == 1: continue

        W = [a for a in units if (c * a % m) < a]

        # Character sums over W
        max_sum = 0
        min_sum = float('inf')
        total = 0
        count = 0

        for j in range(1, phi):
            half_sum = sum(omega**(j*dlog[a]) for a in W)
            mag = abs(half_sum)
            max_sum = max(max_sum, mag)
            min_sum = min(min_sum, mag)
            total += mag
            count += 1

        avg_sum = total / count

        print(f"  Slice n={n} (c={c}):")
        print(f"    max |half-sum|: {max_sum:.4f}")
        print(f"    avg |half-sum|: {avg_sum:.4f}")
        print(f"    min |half-sum|: {min_sum:.4f}")
        print(f"    ratio max/PV:   {max_sum/pv_bound:.4f}")
        print(f"    ratio avg/rand: {avg_sum/random_bound:.4f}")
        break  # just first slice

    print()
