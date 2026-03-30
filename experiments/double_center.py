#!/usr/bin/env python3
"""
Doubly-centered sum: remove both the spectral class bias
AND the mod-3 bias from the residual.

If this converges deeper than F°, the mod-3 elasticity
was masking deeper structure.
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

# Base 10, lag 1
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

# Class means by spectral class R
cls_R = {}
for a in units:
    R = (a - 1) % b
    if R not in cls_R: cls_R[R] = []
    if a in S_table: cls_R[R].append(S_table[a])
mean_R = {R: sum(v)/len(v) for R, v in cls_R.items()}

# S° (singly centered)
S_cent = {}
for a in units:
    if a in S_table:
        R = (a - 1) % b
        S_cent[a] = S_table[a] - mean_R[R]

# Now: class means of S° by p mod 3
cls_mod3 = {1: [], 2: []}
for a in units:
    if a not in S_cent: continue
    k = a % 3
    if k == 0: continue
    cls_mod3[k].append(S_cent[a])

mean_mod3 = {k: sum(v)/len(v) for k, v in cls_mod3.items()}
print(f"Mean of S° by a mod 3:")
print(f"  a ≡ 1 mod 3: mean S° = {mean_mod3[1]:+.6f}")
print(f"  a ≡ 2 mod 3: mean S° = {mean_mod3[2]:+.6f}")
if mean_mod3[2] != 0:
    print(f"  Ratio: {abs(mean_mod3[1]/mean_mod3[2]):.4f}")
else:
    print(f"  Class 2 has zero mean -- bias is one-sided")

# S°° (doubly centered): remove mod-3 bias from S°
S_double = {}
for a in units:
    if a not in S_cent: continue
    k = a % 3
    if k == 0: continue
    S_double[a] = S_cent[a] - mean_mod3[k]

# Now compute F°(s) and F°°(s) at various s values
max_p = 1000000
s_values = [1.0, 0.9, 0.8, 0.7, 0.6, 0.5]

F_single = {s: 0.0 for s in s_values}
F_double = {s: 0.0 for s in s_values}
count = 0

checkpoints = [1000, 5000, 10000, 50000, 78000]
ci = 0

print(f"\n{'primes':>8}", end="")
for s in s_values:
    print(f" {'F°('+str(s)+')':>9} {'F°°('+str(s)+')':>9}", end="")
print()

for p in range(m + 1, max_p):
    if not is_prime(p) or gcd(p, b) != 1: continue
    count += 1

    a = p % m
    if a not in S_cent: continue

    R = (p - 1) % b
    s_c = S_table.get(a, 0) - mean_R.get(R, 0)
    k = p % 3
    s_dc = s_c - mean_mod3.get(k, 0) if k in mean_mod3 else s_c

    lp = log(p)
    for s in s_values:
        w = p ** (-s)
        F_single[s] += s_c * w
        F_double[s] += s_dc * w

    if ci < len(checkpoints) and count >= checkpoints[ci]:
        print(f"{count:>8}", end="")
        for s in s_values:
            print(f" {F_single[s]:>+9.4f} {F_double[s]:>+9.4f}", end="")
        print()
        ci += 1

print(f"\n{'FINAL':>8}", end="")
for s in s_values:
    print(f" {F_single[s]:>+9.4f} {F_double[s]:>+9.4f}", end="")
print(f"  ({count} primes)")
