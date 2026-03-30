#!/usr/bin/env python3
"""
Is |s_hat(chi_1)| = (b-1)/b for all prime bases?
If so, the alignment limit IS the coupling constant.
"""

import cmath
from math import gcd

def primitive_root(n):
    phi = n
    temp = n
    p = 2
    factors = []
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
            if pow(g, phi // f, n) == 1:
                ok = False
                break
        if ok: return g, phi
    return None, phi

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

for b in [3, 5, 7, 11, 13]:
    if not is_prime(b):
        continue

    m = b * b
    units = [a for a in range(1, m) if gcd(a, m) == 1]

    # Compute S values
    S = {}
    for p in range(m + 1, 5000):
        if not is_prime(p) or p % b == 0: continue
        a = p % m
        if a in S: continue
        g = pow(b, 1, p)
        C = collision_count(g, p, b)
        S[a] = C - (p - 1) // b

    # Class means
    cls = {}
    for a in units:
        R = (a - 1) % b
        if R not in cls: cls[R] = []
        cls[R].append(S.get(a, 0))
    cls_mean = {R: sum(v)/len(v) for R, v in cls.items()}

    S_cent = {}
    for a in units:
        R = (a - 1) % b
        S_cent[a] = S.get(a, 0) - cls_mean[R]

    # Characters
    gen, phi = primitive_root(m)
    dlog = {}
    pw = 1
    for k in range(phi):
        dlog[pw] = k
        pw = (pw * gen) % m

    omega = cmath.exp(2j * cmath.pi / phi)
    dl_neg1 = dlog.get(m - 1)

    # Find the dominant odd character (largest |s_hat|)
    best_j = -1
    best_mag = 0

    for j in range(1, phi):
        chi_neg1 = omega ** (j * dl_neg1)
        if chi_neg1.real > -0.5: continue  # skip even

        s_hat = 0
        for a in units:
            if a not in dlog: continue
            s_hat += S_cent.get(a, 0) * omega ** (-j * dlog[a])
        s_hat /= phi

        mag = abs(s_hat)
        if mag > best_mag:
            best_mag = mag
            best_j = j

    predicted = (b - 1) / b

    print(f"base {b:>3}: |ŝ(χ_dominant)| = {best_mag:.6f}  "
          f"(b-1)/b = {predicted:.6f}  "
          f"match = {'YES' if abs(best_mag - predicted) < 0.001 else 'NO'}")
