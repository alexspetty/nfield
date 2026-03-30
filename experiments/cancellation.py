#!/usr/bin/env python3
"""
Look at HOW the cancellation works.
Compute s_hat(chi) * P(0.5, chi) for each odd character.
See which terms cancel.
"""

import cmath
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

def collision_count(g, p, b):
    count = 0
    for r in range(1, p):
        if b * r // p == b * (g * r % p) // p:
            count += 1
    return count

def analyze_base(b, max_p):
    m = b * b
    print(f"\n{'='*60}")
    print(f"BASE {b}, mod {m}")
    print(f"{'='*60}")

    units = [a for a in range(1, m) if gcd(a, m) == 1]

    # Get S values
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
    result = primitive_root(m)
    if result[0] is None:
        print("  Non-cyclic group, skipping")
        return
    gen, phi = result

    dlog = {}
    pw = 1
    for k in range(phi):
        dlog[pw] = k
        pw = (pw * gen) % m

    dl_neg1 = dlog.get(m - 1, None)
    if dl_neg1 is None:
        print("  Can't find -1")
        return

    # Compute s_hat(chi) for each character
    s_hat = []
    for j in range(phi):
        val = 0 + 0j
        for a in units:
            if a not in dlog: continue
            phase = 2 * cmath.pi * j * dlog[a] / phi
            val += S_cent.get(a, 0) * cmath.exp(-1j * phase)
        s_hat.append(val / phi)

    # Compute P(0.5, chi) for each character
    P = [0 + 0j] * phi
    for p in range(m + 1, max_p):
        if not is_prime(p) or gcd(p, m) != 1: continue
        a = p % m
        if a not in dlog: continue
        dl = dlog[a]
        w = 1.0 / (p ** 0.5)
        for j in range(phi):
            phase = 2 * cmath.pi * j * dl / phi
            P[j] += w * cmath.exp(1j * phase)

    # Show the products for odd characters
    print(f"\n  Odd characters: s_hat(chi) * P(0.5, chi)")
    print(f"  {'j':>3} {'|s_hat|':>8} {'|P|':>8} {'product (Re)':>12} {'product (Im)':>12} {'|product|':>10}")

    total = 0 + 0j
    odd_products = []

    for j in range(phi):
        chi_neg1 = cmath.exp(2j * cmath.pi * j * dl_neg1 / phi)
        if chi_neg1.real > -0.5: continue  # skip even
        if j == 0: continue  # skip trivial

        product = s_hat[j] * P[j]
        total += product
        odd_products.append((j, s_hat[j], P[j], product))

        print(f"  {j:>3} {abs(s_hat[j]):>8.4f} {abs(P[j]):>8.4f} {product.real:>+12.4f} {product.imag:>+12.4f} {abs(product):>10.4f}")

    print(f"\n  SUM of all products: {total.real:>+10.4f} {total.imag:>+10.4f}i")
    print(f"  This should equal F°(0.5): {total.real:>+10.4f}")

    # Show cancellation structure
    if len(odd_products) > 2:
        reals = [p[3].real for p in odd_products]
        pos = sum(r for r in reals if r > 0)
        neg = sum(r for r in reals if r < 0)
        print(f"\n  Positive contributions: {pos:>+10.4f}")
        print(f"  Negative contributions: {neg:>+10.4f}")
        print(f"  Cancellation ratio: {abs(neg/pos):.2f}" if pos != 0 else "")

analyze_base(3, 100000)
analyze_base(5, 100000)
analyze_base(7, 100000)
