#!/usr/bin/env python3
"""
Verify |s_hat_dominant| * |tau| = b - 1 across prime bases.
Also check: sum of |s_hat|^2, sum of |s_hat| * |tau|, etc.
"""

import cmath
from math import gcd, pi, sqrt

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

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

def collision_count(g, p, b):
    count = 0
    for r in range(1, p):
        if b * r // p == b * (g * r % p) // p: count += 1
    return count

for b in [3, 5, 7]:
    m = b * b
    units = [a for a in range(1, m) if gcd(a, m) == 1]

    # S values
    S = {}
    for p in range(m + 1, 5000):
        if not is_prime(p) or p % b == 0: continue
        a = p % m
        if a in S: continue
        g = pow(b, 1, p)
        S[a] = collision_count(g, p, b) - (p - 1) // b

    # Class means
    cls = {}
    for a in units:
        R = (a - 1) % b
        if R not in cls: cls[R] = []
        cls[R].append(S.get(a, 0))
    cls_mean = {R: sum(v)/len(v) for R, v in cls.items()}
    S_cent = {a: S.get(a, 0) - cls_mean[(a-1)%b] for a in units}

    # Characters
    gen, phi = primitive_root(m)
    if gen is None:
        print(f"base {b}: no primitive root mod {m}")
        continue

    dlog = {}; pw = 1
    for k in range(phi): dlog[pw] = k; pw = (pw * gen) % m

    omega = cmath.exp(2j * pi / phi)
    dl_neg1 = dlog.get(m - 1)

    print(f"\n{'='*60}")
    print(f"BASE {b}, mod {m}, phi={phi}")
    print(f"{'='*60}")

    # Compute ALL s_hat and tau values
    odd_data = []
    for j in range(1, phi):
        # Parity
        if dl_neg1 is not None:
            chi_neg1 = omega ** (j * dl_neg1)
            if chi_neg1.real > -0.5: continue  # even, skip

        # s_hat
        s_hat = sum(S_cent.get(a, 0) * omega**(-j*dlog[a]) for a in units if a in dlog) / phi

        # Gauss sum tau(chi_j)
        tau = sum(omega**(j*dlog[a]) * cmath.exp(2j*pi*a/m) for a in units if a in dlog)

        mag_s = abs(s_hat)
        mag_t = abs(tau)
        product = mag_s * mag_t

        if mag_s > 0.001:
            odd_data.append((j, s_hat, tau, mag_s, mag_t, product))

    print(f"\nOdd characters with |s_hat| > 0.001:")
    print(f"{'j':>4} {'|s_hat|':>10} {'|tau|':>10} {'|s|*|t|':>10} {'b-1':>6}")

    sum_product = 0
    sum_s2_t2 = 0

    for j, sh, ta, ms, mt, prod in odd_data:
        print(f"{j:>4} {ms:>10.6f} {mt:>10.6f} {prod:>10.6f} {b-1:>6}")
        sum_product += prod
        sum_s2_t2 += ms**2 * mt**2

    print(f"\nSum of |s_hat|*|tau| over odd chars: {sum_product:.6f}")
    print(f"Sum of |s_hat|²*|tau|²:             {sum_s2_t2:.6f}")
    print(f"b - 1 = {b-1}")
    print(f"(b-1)² = {(b-1)**2}")
    print(f"phi/2 * (b-1)/b = {phi/2 * (b-1)/b:.6f}")

    # Parseval: sum |s_hat|^2 * phi = sum |S_cent|^2 / phi
    parseval_lhs = sum(abs(sh)**2 for _, sh, _, _, _, _ in odd_data) * phi
    parseval_rhs = sum(S_cent[a]**2 for a in units) / phi
    print(f"\nParseval check:")
    print(f"  sum |s_hat|² * phi = {parseval_lhs:.6f}")
    print(f"  (1/phi) * sum |S°|² = {parseval_rhs:.6f}")

    # Since |tau| = b for all primitive chars mod b²:
    print(f"\n|tau| = {odd_data[0][4]:.4f} for all odd chars? ", end="")
    all_same_tau = all(abs(mt - b) < 0.01 for _, _, _, _, mt, _ in odd_data)
    print(f"{'YES' if all_same_tau else 'NO'}")

    if all_same_tau:
        # sum |s_hat| * |tau| = b * sum |s_hat|
        sum_s = sum(ms for _, _, _, ms, _, _ in odd_data)
        print(f"  sum |s_hat| (odd) = {sum_s:.6f}")
        print(f"  b * sum |s_hat| = {b * sum_s:.6f}")
        print(f"  sum |s_hat| * |tau| = {sum_product:.6f}")
