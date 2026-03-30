#!/usr/bin/env python3
"""
Do high-fit primes (prime-angle) have smaller |S°| (collision transform)?
If yes: geometric constraint → algebraic bound → deeper convergence.
"""

from math import gcd, pi, cos, sin, sqrt

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def angular_fit(n, constraint_primes):
    """Prime-angle fit: normalized resultant length."""
    k = len(constraint_primes)
    cx, cy = 0.0, 0.0
    for p in constraint_primes:
        theta = 2 * pi * (n % p) / p
        cx += cos(theta)
        cy += sin(theta)
    return sqrt(cx*cx + cy*cy) / k

def angular_burden(n, constraint_primes):
    """Angular variance / dispersion."""
    k = len(constraint_primes)
    phases = [2 * pi * (n % p) / p for p in constraint_primes]
    mean_phase = sum(phases) / k
    return sum((ph - mean_phase)**2 for ph in phases) / k

# Collision transform: S° for base 10 at lag 1
# S depends on p mod 100. Use precomputed table.
def build_S_table(b):
    m = b * b
    S_table = {}
    for p in range(m + 1, 10000):
        if not is_prime(p) or gcd(p, b) != 1:
            continue
        a = p % m
        if a in S_table:
            continue
        g = pow(b, 1, p)
        C = sum(1 for r in range(1, p) if b * r // p == b * (g * r % p) // p)
        Q = (p - 1) // b
        S_table[a] = C - Q
    return S_table, m

print("Building S table for base 10...")
S_table, m = build_S_table(10)

# Class means
units = [a for a in range(1, m) if gcd(a, m) == 1]
cls = {}
for a in units:
    R = (a - 1) % 10
    if R not in cls: cls[R] = []
    cls[R].append(S_table.get(a, 0))
cls_mean = {R: sum(v)/len(v) for R, v in cls.items()}

# Constraint primes for prime-angle (p >= 7, first 10)
constraint_primes = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

print(f"Constraint primes for angular fit: {constraint_primes}")
print(f"\nComputing fit vs |S°| for primes up to 100000...\n")

# For each prime, compute fit and |S°|
data = []
for p in range(101, 100000):
    if not is_prime(p) or gcd(p, 10) != 1:
        continue

    a = p % m
    if a not in S_table:
        continue

    S = S_table[a]
    R = (p - 1) % 10
    S_cent = abs(S - cls_mean[R])

    fit = angular_fit(p, constraint_primes)
    burden = angular_burden(p, constraint_primes)

    data.append((p, fit, burden, S_cent, S))

# Bin by fit and compute mean |S°| in each bin
data.sort(key=lambda x: x[1])  # sort by fit

n_bins = 10
bin_size = len(data) // n_bins

print(f"{'fit range':>20} {'mean |S°|':>12} {'mean burden':>12} {'count':>8}")
print("-" * 56)

for i in range(n_bins):
    start = i * bin_size
    end = (i + 1) * bin_size if i < n_bins - 1 else len(data)

    bin_data = data[start:end]
    mean_fit = sum(d[1] for d in bin_data) / len(bin_data)
    mean_s = sum(d[3] for d in bin_data) / len(bin_data)
    mean_burden = sum(d[2] for d in bin_data) / len(bin_data)
    fit_lo = bin_data[0][1]
    fit_hi = bin_data[-1][1]

    print(f"{fit_lo:>8.4f} - {fit_hi:<8.4f} {mean_s:>12.4f} {mean_burden:>12.4f} {len(bin_data):>8}")

# Overall correlation
n = len(data)
mean_fit_all = sum(d[1] for d in data) / n
mean_s_all = sum(d[3] for d in data) / n

cov = sum((d[1] - mean_fit_all) * (d[3] - mean_s_all) for d in data) / n
var_fit = sum((d[1] - mean_fit_all)**2 for d in data) / n
var_s = sum((d[3] - mean_s_all)**2 for d in data) / n
corr = cov / sqrt(var_fit * var_s) if var_fit > 0 and var_s > 0 else 0

print(f"\nCorrelation(fit, |S°|) = {corr:+.6f}")
print(f"  Negative = high fit → small |S°| (geometric constrains algebraic)")
print(f"  Zero = no relationship")
print(f"  Positive = high fit → large |S°| (opposite)")

# Also check: does |S°| vary at all across primes?
# Remember: S° is determined by p mod 100, so it's periodic.
# Different p mod 100 classes have different S° values.
# The question is: do high-fit primes preferentially land in
# classes with small |S°|?

print(f"\n{'='*56}")
print(f"Key question: does angular fit predict which S° class")
print(f"a prime lands in? Or is it independent?")
print(f"{'='*56}")

# For each S° value, compute mean fit
s_groups = {}
for p, fit, burden, s_cent, S in data:
    if S not in s_groups:
        s_groups[S] = []
    s_groups[S].append(fit)

print(f"\n{'S value':>10} {'|S°|':>8} {'mean fit':>12} {'count':>8}")
for S_val in sorted(s_groups.keys()):
    R_for_S = None
    for a in units:
        if S_table.get(a) == S_val:
            R_for_S = (a - 1) % 10
            break
    s_cent = abs(S_val - cls_mean.get(R_for_S, 0)) if R_for_S is not None else 0
    mean_fit = sum(s_groups[S_val]) / len(s_groups[S_val])
    print(f"{S_val:>10} {s_cent:>8.3f} {mean_fit:>12.6f} {len(s_groups[S_val]):>8}")
