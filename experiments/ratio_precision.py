#!/usr/bin/env python3
"""
High precision analysis of the ratio F°°/mod3.

Questions:
1. Does the ratio approach exactly -1?
2. What is the rate of approach?
3. Does the rate depend on s?
4. Can we express the ratio in closed form?
"""

from math import gcd, log, sqrt

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

b = 10
m = b * b

# Build S table
S_table = {}
for p in range(m + 1, 10000):
    if not is_prime(p) or gcd(p, b) != 1: continue
    a = p % m
    if a in S_table: continue
    g = pow(b, 1, p)
    C = sum(1 for r in range(1, p) if b*r//p == b*(g*r%p)//p)
    S_table[a] = C - (p - 1) // b

units = [a for a in range(1, m) if gcd(a, m) == 1]

cls_R = {}
for a in units:
    R = (a - 1) % b
    if R not in cls_R: cls_R[R] = []
    if a in S_table: cls_R[R].append(S_table[a])
mean_R = {R: sum(v)/len(v) for R, v in cls_R.items()}

S_cent = {}
for a in units:
    if a in S_table:
        S_cent[a] = S_table[a] - mean_R[(a-1) % b]

cls_3 = {}
for a in units:
    if a not in S_cent: continue
    k = a % 3
    if k not in cls_3: cls_3[k] = []
    cls_3[k].append(S_cent[a])
mean_3 = {k: sum(v)/len(v) for k, v in cls_3.items()}

# Use finite determination: no collision counting needed
max_p = 5000000

# Fine grid of s values
s_values = [1.0, 0.95, 0.9, 0.85, 0.8, 0.75, 0.7, 0.65, 0.6, 0.55, 0.5]

F_single = {s: 0.0 for s in s_values}
F_double = {s: 0.0 for s in s_values}
F_mod3 = {s: 0.0 for s in s_values}

count = 0
checkpoints = [10000, 50000, 100000, 200000, 350000]
ci = 0

for p in range(m + 1, max_p):
    if not is_prime(p) or gcd(p, b) != 1: continue
    count += 1

    a = p % m
    if a not in S_cent: continue

    sc = S_cent[a]
    k = p % 3
    mod3_val = mean_3.get(k, 0)
    sc_double = sc - mod3_val

    for s in s_values:
        w = p ** (-s)
        F_single[s] += sc * w
        F_double[s] += sc_double * w
        F_mod3[s] += mod3_val * w

    if ci < len(checkpoints) and count >= checkpoints[ci]:
        print(f"--- {count} primes ---")
        print(f"{'s':>5} {'ratio':>12} {'1+ratio':>12} {'F°':>10}")
        for s in [1.0, 0.8, 0.6, 0.5]:
            if abs(F_mod3[s]) > 0.001:
                ratio = F_double[s] / F_mod3[s]
                print(f"{s:>5.2f} {ratio:>+12.6f} {1+ratio:>12.6f} {F_single[s]:>+10.4f}")
        print()
        ci += 1

# Final detailed analysis
print(f"FINAL: {count} primes")
print(f"\n{'s':>5} {'F°':>12} {'F°°':>12} {'mod3':>12} {'ratio':>12} {'1+ratio':>12}")
for s in s_values:
    if abs(F_mod3[s]) > 0.001:
        ratio = F_double[s] / F_mod3[s]
        dev = 1 + ratio
        print(f"{s:>5.2f} {F_single[s]:>+12.4f} {F_double[s]:>+12.4f} "
              f"{F_mod3[s]:>+12.4f} {ratio:>+12.6f} {dev:>+12.6f}")

# Check: does (1+ratio) scale with s or with 1/|F°°|?
print(f"\nRate analysis: how does (1+ratio) depend on s?")
print(f"{'s':>5} {'1+ratio':>12} {'|F°°|':>12} {'(1+r)*|F°°|':>14} {'F°':>10}")
for s in s_values:
    if abs(F_mod3[s]) > 0.001:
        ratio = F_double[s] / F_mod3[s]
        dev = 1 + ratio
        product = dev * abs(F_double[s])
        print(f"{s:>5.2f} {dev:>+12.6f} {abs(F_double[s]):>12.4f} "
              f"{product:>+14.4f} {F_single[s]:>+10.4f}")
