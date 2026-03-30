#!/usr/bin/env python3
"""
The collision matrix: S(p, b) for all primes p and all bases b.
Two-dimensional object. Rows = primes. Columns = bases.

Questions:
1. What does the row sum (fixed p, all bases) look like?
2. What does the column sum (fixed b, all primes) look like?
3. What does the DOUBLE sum look like?
4. Are there patterns in the 2D structure?
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

def compute_S(p, b):
    if p <= b or p % b == 0: return None
    g = pow(b, 1, p)
    C = sum(1 for r in range(1, p) if b*r//p == b*(g*r%p)//p)
    return C - (p - 1) // b

# Build the matrix for small primes and bases
max_p = 100
max_b = 30

primes = [p for p in range(7, max_p) if is_prime(p)]
bases = list(range(3, max_b + 1))

print("THE COLLISION MATRIX S(p, b)")
print("="*60)

# Row sums (fixed p, sum over b)
print("\nRow sums: sum_b S(p,b)/b for each prime")
print(f"{'p':>5} {'row_sum':>10} {'row/ln(bmax)':>12} {'p%3':>4} {'p%5':>4}")

row_data = []
for p in primes:
    row_sum = 0
    count = 0
    for b in bases:
        S = compute_S(p, b)
        if S is not None:
            row_sum += S / b
            count += 1
    row_data.append((p, row_sum, count))
    ratio = row_sum / log(max_b) if log(max_b) > 0 else 0
    print(f"{p:>5} {row_sum:>+10.4f} {ratio:>12.4f} {p%3:>4} {p%5:>4}")

# Column sums (fixed b, sum over p)
print(f"\nColumn sums: sum_p S(p,b)/p for each base")
print(f"{'b':>5} {'col_sum':>10} {'col/lnln(pmax)':>14} {'primes':>7}")

for b in bases:
    col_sum = 0
    count = 0
    for p in primes:
        S = compute_S(p, b)
        if S is not None:
            col_sum += S / p
            count += 1
    from math import log
    llp = log(log(max_p)) if max_p > 3 else 1
    ratio = col_sum / llp
    print(f"{b:>5} {col_sum:>+10.4f} {ratio:>14.4f} {count:>7}")

# The double sum
print(f"\nDouble sum: sum_b sum_p S(p,b) / (p * b)")
double_sum = 0
for p in primes:
    for b in bases:
        S = compute_S(p, b)
        if S is not None:
            double_sum += S / (p * b)

print(f"  Double sum = {double_sum:+.6f}")

# Now: the CENTERED double sum
# For each base b, compute the class mean and subtract
print(f"\nCentered double sum: sum_b sum_p S°(p,b) / (p * b)")

centered_double = 0
for b in bases:
    # Build S table for this base
    m = b * b
    S_table = {}
    for p in range(m + 1, 5000):
        if not is_prime(p) or gcd(p, b) != 1: continue
        a = p % m
        if a in S_table: continue
        S_table[a] = compute_S(p, b)

    # Class means
    units = [a for a in range(1, m) if gcd(a, m) == 1]
    cls = {}
    for a in units:
        R = (a - 1) % b
        if R not in cls: cls[R] = []
        if a in S_table and S_table[a] is not None:
            cls[R].append(S_table[a])
    cls_mean = {R: sum(v)/len(v) if v else 0 for R, v in cls.items()}

    for p in primes:
        if p <= b or p % b == 0: continue
        S = compute_S(p, b)
        if S is None: continue
        R = (p - 1) % b
        S_cent = S - cls_mean.get(R, 0)
        centered_double += S_cent / (p * b)

print(f"  Centered double sum = {centered_double:+.6f}")

# Pattern: does row sum depend on p mod something?
print(f"\nRow sum by p mod 6:")
mod6_sums = {}
mod6_counts = {}
for p, rs, _ in row_data:
    k = p % 6
    if k not in mod6_sums:
        mod6_sums[k] = 0
        mod6_counts[k] = 0
    mod6_sums[k] += rs
    mod6_counts[k] += 1

for k in sorted(mod6_sums.keys()):
    avg = mod6_sums[k] / mod6_counts[k]
    print(f"  p mod 6 = {k}: avg row sum = {avg:+.4f} (n={mod6_counts[k]})")
