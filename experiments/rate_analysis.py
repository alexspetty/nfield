#!/usr/bin/env python3
"""
Analyze the RATES of divergence/convergence.

F° = (mod-3 piece) + F°°

At s < 1:
- F° converges (computed)
- F°° diverges (computed)
- Therefore mod-3 piece must diverge in the OPPOSITE direction
  and the two divergences must cancel in F°.

Question: how fast does each piece diverge?
If mod-3 diverges like -A log log x and F°° diverges like +A log log x,
they cancel. But do they?
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

# Class means
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

# Mod-3 means of S°
cls_3 = {}
for a in units:
    if a not in S_cent: continue
    k = a % 3
    if k not in cls_3: cls_3[k] = []
    cls_3[k].append(S_cent[a])
mean_3 = {k: sum(v)/len(v) for k, v in cls_3.items()}

print("Mod-3 means of S°:")
for k in sorted(mean_3.keys()):
    print(f"  a ≡ {k} mod 3: mean = {mean_3[k]:+.6f} (n={len(cls_3[k])})")

# Track three sums: F°, F°°, and the mod-3 piece
max_p = 1000000
s_values = [1.0, 0.9, 0.8, 0.7, 0.6, 0.5]

F_single = {s: 0.0 for s in s_values}
F_double = {s: 0.0 for s in s_values}
F_mod3 = {s: 0.0 for s in s_values}  # = F° - F°°

count = 0
checkpoints = [1000, 5000, 10000, 50000, 78000]
ci = 0

print(f"\n{'primes':>8} {'s':>5} {'F°':>10} {'F°°':>10} {'mod3':>10} {'F°-check':>10}")

for p in range(m + 1, max_p):
    if not is_prime(p) or gcd(p, b) != 1: continue
    count += 1

    a = p % m
    if a not in S_cent: continue

    R = (p - 1) % b
    sc = S_table.get(a, 0) - mean_R.get(R, 0)
    k = p % 3
    mod3_val = mean_3.get(k, 0)
    sc_double = sc - mod3_val

    for s in s_values:
        w = p ** (-s)
        F_single[s] += sc * w
        F_double[s] += sc_double * w
        F_mod3[s] += mod3_val * w

    if ci < len(checkpoints) and count >= checkpoints[ci]:
        for s in [1.0, 0.7, 0.5]:
            check = F_mod3[s] + F_double[s]
            print(f"{count:>8} {s:>5.1f} {F_single[s]:>+10.4f} "
                  f"{F_double[s]:>+10.4f} {F_mod3[s]:>+10.4f} "
                  f"{check:>+10.4f}")
        print()
        ci += 1

print(f"\nFINAL ({count} primes):")
print(f"{'s':>5} {'F°':>10} {'F°°':>10} {'mod3':>10} {'ratio F°°/mod3':>15}")
for s in s_values:
    if abs(F_mod3[s]) > 0.001:
        ratio = F_double[s] / F_mod3[s]
    else:
        ratio = float('inf')
    print(f"{s:>5.1f} {F_single[s]:>+10.4f} {F_double[s]:>+10.4f} "
          f"{F_mod3[s]:>+10.4f} {ratio:>+15.4f}")
