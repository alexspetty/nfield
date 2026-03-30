#!/usr/bin/env python3
"""
Verify the class mean formula derivation:
S = 2P - Q where P = sum_{m=1}^Q (1 - mb/p)
Check against actual S values from direct computation.
"""

def isprime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def collision_count(g, p, b):
    """Direct collision count."""
    count = 0
    for r in range(1, p):
        d_r = b * r // p
        gr = (g * r) % p
        d_gr = b * gr // p
        if d_r == d_gr:
            count += 1
    return count

def compute_S_direct(b, lag, p):
    """Compute S = C - Q directly."""
    g = pow(b, lag, p)
    C = collision_count(g, p, b)
    Q = (p - 1) // b
    return C - Q

def equidist_prediction(b, p):
    """Equidistribution prediction for S."""
    R = (p - 1) % b
    Q = (p - 1) // b
    # E[P] = Q - b*Q*(Q+1)/(2*p)
    # S = 2P - Q = Q - b*Q*(Q+1)/p
    return Q - b * Q * (Q + 1) / p

def class_mean_formula(R, b):
    """The conjectured class mean."""
    return (R + 1) / b - 1

# Test for prime bases
for b in [3, 7]:
    print(f"\n=== BASE {b} (prime) ===")
    for R in range(b):
        actual_S = []
        equidist_S = []
        count = 0
        for p in range(b + 2, 2000):
            if not isprime(p) or p % b == 0:
                continue
            if (p - 1) % b != R:
                continue
            S = compute_S_direct(b, 1, p)
            actual_S.append(S)
            equidist_S.append(equidist_prediction(b, p))
            count += 1

        if count > 0:
            mean_actual = sum(actual_S) / count
            mean_equidist = sum(equidist_S) / count
            formula = class_mean_formula(R, b)
            print(f"  R={R}: actual={mean_actual:.4f}  equidist={mean_equidist:.4f}  formula={formula:.4f}  n={count}")

# Test for composite bases
for b in [10, 12]:
    print(f"\n=== BASE {b} (composite) ===")
    from math import gcd
    coprime_R = [R for R in range(b) if gcd(R + 1, b) == 1]
    for R in coprime_R:
        actual_S = []
        equidist_S = []
        count = 0
        for p in range(b + 2, 5000):
            if not isprime(p) or p % b == 0:
                continue
            if (p - 1) % b != R:
                continue
            S = compute_S_direct(b, 1, p)
            actual_S.append(S)
            equidist_S.append(equidist_prediction(b, p))
            count += 1

        if count > 0:
            mean_actual = sum(actual_S) / count
            mean_equidist = sum(equidist_S) / count
            formula = class_mean_formula(R, b)
            print(f"  R={R}: actual={mean_actual:.4f}  equidist={mean_equidist:.4f}  formula={formula:.4f}  n={count}")
