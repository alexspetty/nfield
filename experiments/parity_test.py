#!/usr/bin/env python3
"""
Test: do odd characters converge better than even characters at s=1/2?
Check across multiple bases.
"""

import cmath
from math import gcd, log

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
    from math import gcd
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

def test_base(b, max_p):
    m = b * b
    print(f"\n{'='*60}")
    print(f"BASE {b}, mod {m}, primes to {max_p}")
    print(f"{'='*60}")

    units = [a for a in range(1, m) if gcd(a, m) == 1]
    phi_m = len(units)

    # Try to get primitive root for character construction
    result = primitive_root(m)
    if result[0] is None:
        # Non-cyclic group, use CRT decomposition
        # For simplicity, just compute P(s, chi) via residue class sums
        print(f"  (Z/{m}Z)* is not cyclic, using direct approach")

        # Compute sum_{p = a mod m} 1/p^s for each a
        s_val = 0.5
        class_sum_full = {a: 0.0 for a in units}
        class_sum_half = {a: 0.0 for a in units}
        class_count = {a: 0 for a in units}
        total = 0

        for p in range(m + 1, max_p):
            if not is_prime(p) or gcd(p, m) != 1: continue
            a = p % m
            if a not in class_sum_full: continue
            total += 1
            w = 1.0 / (p ** s_val)
            class_sum_full[a] += w
            if total <= total: # always true, compute half separately below
                class_count[a] += 1

        # recompute with half
        total = 0
        half_total = sum(class_count.values()) // 2
        count = 0
        for p in range(m + 1, max_p):
            if not is_prime(p) or gcd(p, m) != 1: continue
            a = p % m
            if a not in class_sum_half: continue
            count += 1
            if count <= half_total:
                w = 1.0 / (p ** s_val)
                class_sum_half[a] += w

        # Compute drift for each a: |full - half| as fraction
        # Then check: is drift for classes a with a > m/2 ("upper") vs a < m/2 ("lower") different?
        # Actually, check: for the antisymmetric combination f(a) - f(m-a)
        print(f"\n  Paired drift at s={s_val}:")
        print(f"  {'a':>4} {'m-a':>4} {'sum(a)':>10} {'sum(m-a)':>10} {'diff':>10} {'sum':>10}")

        for a in units:
            if a >= m - a: continue
            ma = m - a
            if ma not in class_sum_full: continue
            diff = class_sum_full[a] - class_sum_full[ma]
            total_sum = class_sum_full[a] + class_sum_full[ma]
            print(f"  {a:>4} {ma:>4} {class_sum_full[a]:>10.4f} {class_sum_full[ma]:>10.4f} {diff:>+10.4f} {total_sum:>10.4f}")

        return

    gen, phi = result
    print(f"  Generator: {gen}, phi({m}) = {phi}")

    # Build discrete log
    dlog = {}
    pw = 1
    for k in range(phi):
        dlog[pw] = k
        pw = (pw * gen) % m

    # Compute P(s, chi_j) at s = 0.5 for each character j
    # and at s = 0.5 with half the primes
    P_full = [0.0 + 0j] * phi
    P_half = [0.0 + 0j] * phi
    total = 0
    half_done = False

    # First count total primes
    prime_count = sum(1 for p in range(m+1, max_p) if is_prime(p) and gcd(p, m) == 1)
    half = prime_count // 2

    count = 0
    for p in range(m + 1, max_p):
        if not is_prime(p) or gcd(p, m) != 1: continue
        count += 1
        a = p % m
        if a not in dlog: continue
        dl = dlog[a]
        w = 1.0 / (p ** 0.5)

        for j in range(phi):
            phase = 2 * cmath.pi * j * dl / phi
            val = w * cmath.exp(1j * phase)
            P_full[j] += val
            if count <= half:
                P_half[j] += val

    # Classify characters by parity
    # chi(-1) = chi(m-1). If m-1 is in dlog: chi_j(-1) = exp(2*pi*i*j*dlog[m-1]/phi)
    if m - 1 in dlog:
        dl_neg1 = dlog[m - 1]
    else:
        print("  Cannot find -1 in group")
        return

    print(f"\n  {'j':>3} {'chi(-1)':>8} {'parity':>7} {'|P(0.5)|':>10} {'drift':>8}")

    odd_drifts = []
    even_drifts = []

    for j in range(phi):
        chi_neg1 = cmath.exp(2j * cmath.pi * j * dl_neg1 / phi)
        parity = "odd" if chi_neg1.real < -0.5 else "even"

        mag = abs(P_full[j])
        drift = abs(P_full[j] - P_half[j])

        if j == 0:
            label = " (trivial)"
        else:
            label = ""

        print(f"  {j:>3} {chi_neg1.real:>+8.1f} {parity:>7} {mag:>10.3f} {drift:>8.4f}{label}")

        if j > 0:
            if parity == "odd":
                odd_drifts.append(drift)
            else:
                even_drifts.append(drift)

    if odd_drifts and even_drifts:
        avg_odd = sum(odd_drifts) / len(odd_drifts)
        avg_even = sum(even_drifts) / len(even_drifts)
        print(f"\n  Average drift: odd = {avg_odd:.4f} ({len(odd_drifts)} chars)")
        print(f"  Average drift: even = {avg_even:.4f} ({len(even_drifts)} chars)")
        print(f"  Ratio even/odd = {avg_even/avg_odd:.2f}x")
        if avg_odd < avg_even:
            print(f"  >>> ODD CHARACTERS CONVERGE BETTER <<<")
        else:
            print(f"  >>> EVEN CHARACTERS CONVERGE BETTER <<<")

test_base(3, 100000)
test_base(5, 100000)
test_base(7, 100000)
