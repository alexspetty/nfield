#!/usr/bin/env python3
"""
Sweep bases. For each base b, compute the collision transform
coefficient and the half-sum. Look for structure across bases
that isn't visible from any single base.

Ideas:
1. For fixed prime p, how does S(p) vary across bases?
2. Do the half-sums across bases cancel?
3. Is there a base-sum that converges faster than any single base?
"""

from math import gcd, floor, sqrt, pi
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

def compute_S(p, b):
    """Collision deviation S at lag 1 for prime p in base b."""
    if p <= b or p % b == 0: return None
    g = pow(b, 1, p)
    C = sum(1 for r in range(1, p) if b*r//p == b*(g*r%p)//p)
    Q = (p - 1) // b
    return C - Q

# Experiment 1: Fixed prime, sweep bases
print("="*60)
print("EXPERIMENT 1: Fixed prime p=97, S across bases")
print("="*60)

p = 97
print(f"\np = {p}")
print(f"{'base':>6} {'m=b^2':>8} {'a=p%m':>8} {'S':>6} {'Q':>6} {'R':>6}")

for b in range(3, 40):
    if p % b == 0: continue
    S = compute_S(p, b)
    if S is None: continue
    m = b * b
    a = p % m
    Q = (p - 1) // b
    R = (p - 1) % b
    print(f"{b:>6} {m:>8} {a:>8} {S:>6} {Q:>6} {R:>6}")

# Experiment 2: Sum S across bases (the "base sum")
print(f"\n{'='*60}")
print(f"EXPERIMENT 2: Base sum = sum_b S_b(p) / b for primes")
print(f"{'='*60}")

print(f"\n{'p':>6} {'base_sum':>12} {'num_bases':>10}")

for p in [7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]:
    if not is_prime(p): continue
    base_sum = 0
    count = 0
    for b in range(3, p):
        if p % b == 0: continue
        S = compute_S(p, b)
        if S is not None:
            base_sum += S / b
            count += 1
    print(f"{p:>6} {base_sum:>+12.4f} {count:>10}")

# Experiment 3: Does the base sum grow or stabilize?
print(f"\n{'='*60}")
print(f"EXPERIMENT 3: Running base sum as b increases (p=97)")
print(f"{'='*60}")

p = 97
running = 0
print(f"\n{'b_max':>6} {'running_sum':>14} {'running/log(b)':>14}")

for b in range(3, p):
    if p % b == 0: continue
    S = compute_S(p, b)
    if S is not None:
        running += S / b
    if b in [5, 10, 20, 30, 40, 50, 60, 70, 80, 90, 96]:
        from math import log
        print(f"{b:>6} {running:>+14.4f} {running/log(b):>14.4f}")

# Experiment 4: Cross-base collision transform
# For each prime p, its "base signature" is the vector
# (S_3(p), S_5(p), S_7(p), ...) across all bases
print(f"\n{'='*60}")
print(f"EXPERIMENT 4: Do primes with same p mod 9 have same base signature?")
print(f"{'='*60}")

bases_to_check = [3, 5, 7, 11, 13]
print(f"\nBases: {bases_to_check}")
print(f"{'p':>6} {'p%9':>5}", end="")
for b in bases_to_check:
    print(f" {'S_'+str(b):>6}", end="")
print()

for p in range(11, 200):
    if not is_prime(p): continue
    skip = False
    for b in bases_to_check:
        if p % b == 0: skip = True
    if skip: continue

    print(f"{p:>6} {p%9:>5}", end="")
    for b in bases_to_check:
        S = compute_S(p, b)
        print(f" {S:>6}" if S is not None else f" {'--':>6}", end="")
    print()
