#!/usr/bin/env python3
"""
Do collision transforms from different bases span the character space?

For each base b, the collision transform gives coefficients s_hat(chi)
for characters mod b^2. Different bases give characters at different
moduli. But characters at different moduli can be "lifted" to a common
modulus (their LCM).

Simpler test: for a FIXED modulus q, compute the collision transforms
from all bases b whose b^2 divides q (or whose characters factor
through q). Check if the coefficient vectors span the character space
mod q.

Start with q = 9 (base 3), q = 25 (base 5), q = 100 (base 10).
"""

from math import gcd
import cmath

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
        d_r = b * r // p
        gr = (g * r) % p
        d_gr = b * gr // p
        if d_r == d_gr:
            count += 1
    return count

def compute_S_table(b, max_p=5000):
    """Compute S(a) for all coprime a mod b^2."""
    m = b * b
    table = {}
    for p in range(m + 1, max_p):
        if not is_prime(p) or p % b == 0:
            continue
        a = p % m
        if a in table:
            continue
        g = pow(b, 1, p)
        C = collision_count(g, p, b)
        Q = (p - 1) // b
        table[a] = C - Q
    return table, m

# For base 3: characters mod 9
# phi(9) = 6, so 5 non-trivial characters
print("=== BASE 3, mod 9 ===")
S3, m3 = compute_S_table(3)
units3 = sorted([a for a in range(1, m3) if gcd(a, m3) == 1])
print(f"Units mod {m3}: {units3}")
print(f"S values: {[S3.get(a, '?') for a in units3]}")

# Class means
cls_mean = {}
for R in range(3):
    vals = [S3[a] for a in units3 if (a - 1) % 3 == R]
    if vals:
        cls_mean[R] = sum(vals) / len(vals)
        print(f"  R={R}: mean = {cls_mean[R]:.4f}, values = {vals}")

# S° values
S_centered = {}
for a in units3:
    R = (a - 1) % 3
    S_centered[a] = S3[a] - cls_mean[R]

print(f"\nS° values: {[f'{S_centered[a]:.3f}' for a in units3]}")

# The collision transform vector for base 3 is just S°(a) for a in units mod 9
# This is a vector in R^5 (one dimension removed by centering)

print(f"\n=== Checking rank across bases ===\n")

# For the rank test, let's work at a common modulus.
# Every collision transform at base b lives on (Z/b^2Z)*.
# For bases 3, 5: LCM(9, 25) = 225. phi(225) = 120.
# That's too big. Let's think differently.

# Simpler approach: for each base b, the collision transform
# produces a vector of length phi(b^2) - 1 (excluding trivial char).
# These are vectors in DIFFERENT spaces for different b.
# They can't be directly compared.

# BUT: the penetration depth question is about individual L-functions.
# L(s, chi) for chi mod q appears in the collision transform at base b
# whenever b^2 is a multiple of q's conductor (or related).

# For our purposes: the key question is whether different bases
# give INDEPENDENT information about the same L-functions.

# Test: for characters mod 3 (conductor 3), these appear in:
#   base 3 (mod 9), base 6 (mod 36), base 9 (mod 81), etc.
# The coefficients s_hat(chi) will differ across bases.

# Let's compute: for each character chi mod 3, what is its
# contribution in the collision transforms at bases 3, 5, 7, 10?

# Characters mod 3: trivial and chi_3 (the unique non-trivial char mod 3)
# chi_3(1) = 1, chi_3(2) = -1

# In base 3 (mod 9): characters mod 9 include "lifts" of chi_3.
# The characters mod 9 that factor through mod 3 are:
#   chi such that chi(a) depends only on a mod 3.

# This is getting complicated. Let me just compute the coefficient
# vectors and see if they give independent information.

# More direct test: compute F°(s) at s=0.5 for individual
# character components, not the full sum.

print("Individual character sums P(s, chi) at s = 0.5")
print("Base 3, characters mod 9\n")

# For base 3: manually construct characters mod 9
# (Z/9Z)* = {1, 2, 4, 5, 7, 8}, cyclic of order 6, generator 2
# 2^0=1, 2^1=2, 2^2=4, 2^3=8, 2^4=7, 2^5=5

gen = 2
dlog = {}
pw = 1
for k in range(6):
    dlog[pw] = k
    pw = (pw * gen) % 9

print(f"Discrete log table mod 9: {dlog}")

# 6 characters: chi_j(a) = exp(2*pi*i*j*dlog[a]/6) for j=0,...,5
# j=0 is trivial

# Compute P(0.5, chi_j) = sum_p chi_j(p) / sqrt(p)
# for primes p with gcd(p, 3) = 1, up to some limit

max_p = 50000
P_re = [0.0] * 6
P_im = [0.0] * 6

for p in range(5, max_p):
    if not is_prime(p) or p % 3 == 0:
        continue
    a = p % 9
    dl = dlog.get(a, None)
    if dl is None:
        continue
    w = 1.0 / (p ** 0.5)
    for j in range(6):
        phase = 2 * cmath.pi * j * dl / 6
        P_re[j] += w * cmath.cos(phase)
        P_im[j] += w * cmath.sin(phase)

print(f"\nP(0.5, chi_j) for j=0,...,5 ({max_p} prime limit):")
for j in range(6):
    mag = (P_re[j]**2 + P_im[j]**2)**0.5
    if j == 0:
        print(f"  j={j} (trivial): Re={P_re[j]:+8.3f}  Im={P_im[j]:+8.3f}  |P|={mag:.3f}  (DIVERGES)")
    else:
        print(f"  j={j}: Re={P_re[j]:+8.3f}  Im={P_im[j]:+8.3f}  |P|={mag:.3f}")

# Now check: do the individual non-trivial P(0.5, chi_j) converge?
# Compute at half the range too
P_half_re = [0.0] * 6
P_half_im = [0.0] * 6
count = 0
half_count = 0
total = sum(1 for p in range(5, max_p) if is_prime(p) and p % 3 != 0)

for p in range(5, max_p):
    if not is_prime(p) or p % 3 == 0:
        continue
    count += 1
    a = p % 9
    dl = dlog.get(a, None)
    if dl is None:
        continue
    w = 1.0 / (p ** 0.5)
    if count <= total // 2:
        for j in range(6):
            phase = 2 * cmath.pi * j * dl / 6
            P_half_re[j] += w * cmath.cos(phase)
            P_half_im[j] += w * cmath.sin(phase)

print(f"\nDrift (full - half) at s=0.5:")
for j in range(1, 6):
    drift_re = abs(P_re[j] - P_half_re[j])
    drift_im = abs(P_im[j] - P_half_im[j])
    drift = (drift_re**2 + drift_im**2)**0.5
    print(f"  j={j}: drift = {drift:.4f}")
