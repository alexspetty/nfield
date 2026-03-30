#!/usr/bin/env python3
"""
Sign structure across multiple bases.
For each base b, compute the odd characters mod b^2,
the collision transform coefficients, and the sign split.
"""

from math import gcd, pi, cos, sin
from collections import defaultdict

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
    """Find primitive root mod n, return (g, phi) or (None, phi)."""
    units = [a for a in range(1, n) if gcd(a, n) == 1]
    phi = len(units)
    if phi == 0:
        return None, 0

    # Factor phi
    temp = phi
    prime_factors = []
    for p in range(2, int(temp**0.5) + 2):
        if temp % p == 0:
            prime_factors.append(p)
            while temp % p == 0:
                temp //= p
    if temp > 1:
        prime_factors.append(temp)

    for g in range(2, n):
        if gcd(g, n) != 1:
            continue
        ok = True
        for p in prime_factors:
            if pow(g, phi // p, n) == 1:
                ok = False
                break
        if ok:
            return g, phi
    return None, phi

def build_chars_cyclic(m, g, phi):
    """Build all characters for cyclic group with generator g."""
    dlog = {}
    val = 1
    for k in range(phi):
        dlog[val] = k
        val = val * g % m

    chars = []
    for j in range(phi):
        chi = {}
        for a in range(m):
            if gcd(a, m) != 1:
                chi[a] = 0
            else:
                k = dlog[a]
                angle = 2 * pi * j * k / phi
                chi[a] = complex(cos(angle), sin(angle))

        val_minus1 = chi[m - 1]
        is_odd = abs(val_minus1 - (-1)) < 1e-6

        chars.append({'index': j, 'chi': chi, 'is_odd': is_odd})
    return chars

def run_base(b, max_prime=2000000):
    m = b * b

    # Check for primitive root
    g, phi = primitive_root(m)
    if g is None:
        # Non-cyclic group, skip for now
        return None

    # Build S table
    S_table = {}
    for p in range(m + 1, min(80000, max_prime)):
        if not is_prime(p) or gcd(p, b) != 1:
            continue
        a = p % m
        if a in S_table:
            continue
        C = sum(1 for r in range(1, p)
                if b * r // p == b * (b * r % p) // p)
        S_table[a] = C - (p - 1) // b

    units = [a for a in range(1, m) if gcd(a, m) == 1]

    # Class means for centering
    cls = defaultdict(list)
    for a in units:
        if a in S_table:
            cls[(a - 1) % b].append(S_table[a])
    mean_R = {R: sum(v)/len(v) for R, v in cls.items()}

    S_cent = {}
    for a in units:
        if a in S_table:
            S_cent[a] = S_table[a] - mean_R[(a - 1) % b]

    # Build characters
    chars = build_chars_cyclic(m, g, phi)
    odd_chars = [c for c in chars if c['is_odd']]

    if len(odd_chars) == 0:
        return None

    # Compute s_hat
    for c in odd_chars:
        chi = c['chi']
        s_hat = sum(S_cent.get(a, 0) * chi.get(a, 0).conjugate()
                    for a in units) / phi
        c['s_hat'] = complex(s_hat)

    # Compute P(s, chi) at s = 1.0, 0.7, 0.5
    s_values = [1.0, 0.7, 0.5]
    for c in odd_chars:
        c['P'] = {s: complex(0) for s in s_values}

    count = 0
    for p in range(m + 1, max_prime):
        if not is_prime(p) or gcd(p, b) != 1:
            continue
        count += 1
        a = p % m
        for c in odd_chars:
            chi_p = c['chi'].get(a, 0)
            if chi_p == 0: continue
            for s in s_values:
                c['P'][s] += chi_p * p ** (-s)

    results = {}
    for s in s_values:
        pos = sum(1 for c in odd_chars
                  if (c['s_hat'] * c['P'][s]).real >= -1e-10)
        neg = len(odd_chars) - pos
        total = sum((c['s_hat'] * c['P'][s]).real for c in odd_chars)
        results[s] = (pos, neg, total)

    return {
        'b': b, 'm': m, 'phi': phi,
        'n_odd': len(odd_chars),
        'primes': count,
        'results': results
    }

# Run across bases
print(f"{'base':>5} {'m':>5} {'phi':>4} {'odd':>4} {'primes':>7} | "
      f"{'s=1.0':>12} {'s=0.7':>12} {'s=0.5':>12} | "
      f"{'net s=1':>8} {'net s=.5':>8}")

for b in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
    r = run_base(b)
    if r is None:
        print(f"{b:>5}  (no primitive root or no odd chars)")
        continue

    res = r['results']
    line = f"{r['b']:>5} {r['m']:>5} {r['phi']:>4} {r['n_odd']:>4} {r['primes']:>7} | "
    for s in [1.0, 0.7, 0.5]:
        p, n, t = res[s]
        line += f"{p:>3}+/{n:>2}-    "
    line += f"| {res[1.0][2]:>+8.3f} {res[0.5][2]:>+8.3f}"
    print(line)
