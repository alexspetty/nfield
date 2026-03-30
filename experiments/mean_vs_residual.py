#!/usr/bin/env python3
"""
Is the 2:1 ratio from the class means or the residual?

For each base b, decompose S(p,b) = class_mean + S°(p,b).
Sweep each part separately. See which one carries the 2:1.
"""

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

def compute_S(p, b):
    if p <= b or p % b == 0: return None
    g = pow(b, 1, p)
    C = sum(1 for r in range(1, p) if b*r//p == b*(g*r%p)//p)
    return C - (p - 1) // b

max_p = 200
bases = list(range(3, 41))
primes = [p for p in range(7, max_p) if is_prime(p)]

# For each base, compute class means
class_means = {}  # class_means[b][R] = mean
for b in bases:
    m = b * b
    S_table = {}
    for p in range(m + 1, 5000):
        if not is_prime(p) or gcd(p, b) != 1: continue
        a = p % m
        if a in S_table: continue
        S_table[a] = compute_S(p, b)

    units = [a for a in range(1, m) if gcd(a, m) == 1]
    cls = {}
    for a in units:
        R = (a - 1) % b
        if R not in cls: cls[R] = []
        if a in S_table and S_table[a] is not None:
            cls[R].append(S_table[a])

    class_means[b] = {}
    for R, vals in cls.items():
        if vals:
            class_means[b][R] = sum(vals) / len(vals)

# Now sweep: separate mean part and residual part
mean_sums = {1: 0, 2: 0}
resid_sums = {1: 0, 2: 0}
total_sums = {1: 0, 2: 0}
counts = {1: 0, 2: 0}

for p in primes:
    k = p % 3
    if k == 0: continue

    mean_row = 0
    resid_row = 0
    total_row = 0

    for b in bases:
        S = compute_S(p, b)
        if S is None: continue
        R = (p - 1) % b
        cm = class_means.get(b, {}).get(R, 0)
        mean_row += cm / b
        resid_row += (S - cm) / b
        total_row += S / b

    mean_sums[k] += mean_row
    resid_sums[k] += resid_row
    total_sums[k] += total_row
    counts[k] += 1

print("Source of the 2:1 ratio")
print("="*60)

avg_mean_1 = mean_sums[1] / counts[1]
avg_mean_2 = mean_sums[2] / counts[2]
avg_resid_1 = resid_sums[1] / counts[1]
avg_resid_2 = resid_sums[2] / counts[2]
avg_total_1 = total_sums[1] / counts[1]
avg_total_2 = total_sums[2] / counts[2]

print(f"\np ≡ 1 mod 3 (n={counts[1]}):")
print(f"  Mean part:     {avg_mean_1:+.4f}")
print(f"  Residual part: {avg_resid_1:+.4f}")
print(f"  Total:         {avg_total_1:+.4f}")

print(f"\np ≡ 2 mod 3 (n={counts[2]}):")
print(f"  Mean part:     {avg_mean_2:+.4f}")
print(f"  Residual part: {avg_resid_2:+.4f}")
print(f"  Total:         {avg_total_2:+.4f}")

mean_total = abs(avg_mean_1) + abs(avg_mean_2)
resid_total = abs(avg_resid_1) + abs(avg_resid_2)

print(f"\nFraction from MEANS:")
print(f"  p ≡ 1: {abs(avg_mean_1)/mean_total:.4f}")
print(f"  p ≡ 2: {abs(avg_mean_2)/mean_total:.4f}")

if resid_total > 0.001:
    print(f"\nFraction from RESIDUALS:")
    print(f"  p ≡ 1: {abs(avg_resid_1)/resid_total:.4f}")
    print(f"  p ≡ 2: {abs(avg_resid_2)/resid_total:.4f}")
else:
    print(f"\nResiduals are near zero: {resid_total:.6f}")
