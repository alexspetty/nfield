#!/usr/bin/env python3
"""
Why are the positive terms stronger?
Check if large |s_hat| correlates with positive Re(s_hat * P).
Also: decompose the total into contribution by magnitude tier.
"""

from math import gcd, pi, cos, sin, atan2
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

b = 10
m = b * b

# Build S table
S_table = {}
for p in range(m + 1, 50000):
    if not is_prime(p) or gcd(p, b) != 1: continue
    a = p % m
    if a in S_table: continue
    C = sum(1 for r in range(1, p) if b*r//p == b*(b*r%p)//p)
    S_table[a] = C - (p - 1) // b

units = [a for a in range(1, m) if gcd(a, m) == 1]
phi = len(units)

cls = defaultdict(list)
for a in units:
    if a in S_table:
        cls[(a-1) % b].append(S_table[a])
mean_R = {R: sum(v)/len(v) for R, v in cls.items()}

S_cent = {}
for a in units:
    if a in S_table:
        S_cent[a] = S_table[a] - mean_R[(a-1) % b]

# Characters mod 100 = (Z/4Z)* x (Z/25Z)*
# Generator mod 25: g=2, order 20
# Generator mod 4: g=3, order 2
g25 = 2
dlog25 = {}
val = 1
for i in range(20):
    dlog25[val] = i
    val = val * g25 % 25
dlog4 = {1: 0, 3: 1}

results = []
for j in range(2):
    for k in range(20):
        chi = {}
        for a in range(100):
            if gcd(a, 100) != 1:
                chi[a] = 0
            else:
                angle = pi * j * dlog4[a % 4] + 2*pi*k*dlog25[a%25]/20
                chi[a] = complex(cos(angle), sin(angle))

        if abs(chi[99] - (-1)) > 1e-6: continue  # odd only

        s_hat = sum(S_cent.get(a,0) * chi[a].conjugate() for a in units) / phi

        # P at s=0.5
        P = complex(0)
        for p in range(m+1, 5000000):
            if not is_prime(p) or gcd(p, b) != 1: continue
            a = p % m
            chi_p = chi.get(a, 0)
            if chi_p == 0: continue
            P += chi_p * p**(-0.5)

        prod = s_hat * P
        results.append({
            'j': j, 'k': k,
            's_hat': complex(s_hat),
            'P': P,
            'prod': prod,
            'sign': '+' if prod.real >= -1e-10 else '-'
        })
        break  # only need to compute primes once
    # Actually need to compute for each character separately
    # Let me restructure

# Redo properly: accumulate all P simultaneously
chars = []
for j in range(2):
    for k in range(20):
        chi = {}
        for a in range(100):
            if gcd(a, 100) != 1:
                chi[a] = 0
            else:
                angle = pi * j * dlog4[a%4] + 2*pi*k*dlog25[a%25]/20
                chi[a] = complex(cos(angle), sin(angle))
        if abs(chi[99] - (-1)) > 1e-6: continue
        s_hat = sum(S_cent.get(a,0) * chi[a].conjugate() for a in units) / phi
        chars.append({'j': j, 'k': k, 'chi': chi, 's_hat': complex(s_hat), 'P': complex(0)})

for p in range(m+1, 5000000):
    if not is_prime(p) or gcd(p, b) != 1: continue
    a = p % m
    for c in chars:
        chi_p = c['chi'].get(a, 0)
        if chi_p == 0: continue
        c['P'] += chi_p * p**(-0.5)

print("=== Sorted by |s_hat| (largest first) ===")
print(f"{'j':>2} {'k':>3} {'|sh|':>7} {'|P|':>7} {'Re(sh*P)':>10} {'|sh*P|':>10} {'sign':>5} {'%contrib':>8}")

total_pos = sum((c['s_hat']*c['P']).real for c in chars if (c['s_hat']*c['P']).real > 0)
total_neg = sum((c['s_hat']*c['P']).real for c in chars if (c['s_hat']*c['P']).real < 0)
total = sum((c['s_hat']*c['P']).real for c in chars)

for c in sorted(chars, key=lambda x: -abs(x['s_hat'])):
    prod = c['s_hat'] * c['P']
    sign = '+' if prod.real >= -1e-10 else '-'
    pct = 100 * prod.real / total if abs(total) > 1e-10 else 0
    print(f"{c['j']:>2} {c['k']:>3} {abs(c['s_hat']):>7.4f} {abs(c['P']):>7.4f} "
          f"{prod.real:>+10.4f} {abs(prod):>10.4f} {sign:>5} {pct:>+7.1f}%")

print(f"\nTotal positive: {total_pos:+.4f}")
print(f"Total negative: {total_neg:+.4f}")
print(f"Net:            {total:+.4f}")
print(f"Ratio pos/|neg|: {total_pos/abs(total_neg):.3f}")

# Breakdown by coefficient size
print("\n=== By coefficient magnitude tier ===")
large = [c for c in chars if abs(c['s_hat']) > 0.5]
medium = [c for c in chars if 0.1 < abs(c['s_hat']) <= 0.5]
small = [c for c in chars if abs(c['s_hat']) <= 0.1]

for label, group in [('large |sh|>0.5', large),
                      ('medium 0.1<|sh|<0.5', medium),
                      ('small |sh|<0.1', small)]:
    if not group: continue
    pos = sum(1 for c in group if (c['s_hat']*c['P']).real >= -1e-10)
    neg = len(group) - pos
    net = sum((c['s_hat']*c['P']).real for c in group)
    print(f"  {label}: {len(group)} chars, {pos}+/{neg}-, net={net:+.4f}")

# Check: do the paired characters (k and 20-k) always agree?
print("\n=== Conjugate pair contributions ===")
seen = set()
pair_contribs = []
for c in chars:
    j, k = c['j'], c['k']
    if (j,k) in seen: continue
    k2 = (20-k) % 20
    partner = None
    for c2 in chars:
        if c2['j'] == j and c2['k'] == k2 and (j,k2) != (j,k):
            partner = c2
            break

    prod = c['s_hat'] * c['P']
    if partner:
        prod2 = partner['s_hat'] * partner['P']
        pair_re = prod.real + prod2.real
        print(f"  ({j},{k:>2})+({j},{k2:>2}): Re = {pair_re:+.4f}  "
              f"[{prod.real:+.4f} + {prod2.real:+.4f}]")
        seen.add((j,k))
        seen.add((j,k2))
        pair_contribs.append(pair_re)
    else:
        print(f"  ({j},{k:>2}) self:     Re = {prod.real:+.4f}")
        seen.add((j,k))
        pair_contribs.append(prod.real)

print(f"\nPair contributions (sorted):")
for v in sorted(pair_contribs, reverse=True):
    print(f"  {v:+.4f}")
