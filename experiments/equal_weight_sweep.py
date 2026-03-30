#!/usr/bin/env python3
"""
Strip the 1/b weighting. Give all bases equal weight.
Does p mod 3 still dominate?

Also try: weight by 1/sqrt(b), weight by 1, weight by b.
See what changes and what doesn't.
"""

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

def compute_S(p, b):
    if p <= b or p % b == 0: return None
    g = pow(b, 1, p)
    C = sum(1 for r in range(1, p) if b*r//p == b*(g*r%p)//p)
    return C - (p - 1) // b

max_p = 200
max_b = 40
primes = [p for p in range(7, max_p) if is_prime(p)]
bases = list(range(3, max_b + 1))

weightings = {
    "1/b": lambda b: 1.0/b,
    "equal": lambda b: 1.0,
    "1/sqrt(b)": lambda b: 1.0/b**0.5,
    "1/b^2": lambda b: 1.0/(b*b),
}

for wname, wfunc in weightings.items():
    print(f"\n{'='*60}")
    print(f"Weighting: {wname}")
    print(f"{'='*60}")

    # Compute row sums with this weighting
    mod3_sums = {1: [], 2: []}

    for p in primes:
        row_sum = 0
        for b in bases:
            S = compute_S(p, b)
            if S is not None:
                row_sum += S * wfunc(b)
        mod3_sums[p % 3 if p % 3 != 0 else 3].append(row_sum)

    avg1 = sum(mod3_sums[1]) / len(mod3_sums[1])
    avg2 = sum(mod3_sums[2]) / len(mod3_sums[2])
    total = abs(avg1) + abs(avg2)
    frac1 = abs(avg1) / total if total > 0 else 0
    frac2 = abs(avg2) / total if total > 0 else 0

    print(f"  p ≡ 1 mod 3: avg = {avg1:+.4f}  fraction = {frac1:.4f}")
    print(f"  p ≡ 2 mod 3: avg = {avg2:+.4f}  fraction = {frac2:.4f}")
    print(f"  Ratio: {abs(avg1/avg2):.4f}")
    print(f"  2/3 test: frac1 ≈ 2/3? {abs(frac1 - 2/3) < 0.05}")

    # Also check mod 5
    mod5_sums = {}
    for p in primes:
        row_sum = 0
        for b in bases:
            S = compute_S(p, b)
            if S is not None:
                row_sum += S * wfunc(b)
        k = p % 5
        if k == 0: continue
        if k not in mod5_sums: mod5_sums[k] = []
        mod5_sums[k].append(row_sum)

    print(f"\n  By p mod 5:")
    for k in sorted(mod5_sums.keys()):
        avg = sum(mod5_sums[k]) / len(mod5_sums[k])
        print(f"    p ≡ {k} mod 5: avg = {avg:+.4f}  (n={len(mod5_sums[k])})")

    # And mod 7
    mod7_sums = {}
    for p in primes:
        row_sum = 0
        for b in bases:
            S = compute_S(p, b)
            if S is not None:
                row_sum += S * wfunc(b)
        k = p % 7
        if k == 0: continue
        if k not in mod7_sums: mod7_sums[k] = []
        mod7_sums[k].append(row_sum)

    print(f"\n  By p mod 7:")
    for k in sorted(mod7_sums.keys()):
        avg = sum(mod7_sums[k]) / len(mod7_sums[k])
        print(f"    p ≡ {k} mod 7: avg = {avg:+.4f}  (n={len(mod7_sums[k])})")
