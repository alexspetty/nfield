#!/usr/bin/env python3
"""
The lag as a zoom lens.

At lag ell, the collision invariant S_ell(n) depends on
n mod b^{ell+1}. The digit function is floor(b^ell * r / n).

At lag 1: resolution b^2 = 100. The observer has 100 bins.
At lag 2: resolution b^3 = 1000. The observer has 1000 bins.
At lag k: resolution b^{k+1}. Exponentially finer.

The 1/p wall exists because the observer has only b bins
and p > b. But at higher lags, the number of effective
bins grows as b^ell. When b^ell > p, the observer can
resolve the p-structure.

KEY: S_ell(n) is determined by n mod b^{ell+1}. We KNOW n.
So we know S_ell(n) at every lag without any computation.

The decomposition theorem at lag ell gives L-values for
characters mod b^{ell+1}. More characters, more L-values,
finer resolution.

Question: does the sequence S_1(n), S_2(n), ... across
lags carry factoring information that no single lag has?
"""
import math

b = 10
n = 91  # 7 x 13

print(f"n = {n} = 7 x 13, base {b}")
print(f"\nCollision invariant at increasing lags:")

for ell in range(1, 6):
    m = b ** (ell + 1)
    a = n % m  # residue class

    # Compute S_ell: collision count at multiplier b^ell
    g = pow(b, ell, n)  # b^ell mod n
    C = 0
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        d1 = (b ** ell) * r // n
        gr = g * r % n
        d2 = (b ** ell) * gr // n
        if d1 == d2:
            C += 1
    Q = (n - 1) // (b ** ell) if b ** ell <= n else 0
    S = C - Q

    # Also: what is the effective number of bins?
    n_bins = min(b ** ell, n)

    print(f"  ell={ell}: m=b^{ell+1}={m:>8}, n mod m = {a:>8}, "
          f"g=b^ell mod n = {g:>3}, C={C:>3}, Q={Q:>3}, S={S:>+4}, "
          f"bins={n_bins}")

# Now: does the sequence of S values distinguish 91
# from a prime p = 91? (No prime is 91, but take p=97
# which is ≡ 97 mod 100, different from 91 mod 100.
# Take p=191 ≡ 91 mod 100.)
print(f"\nComparison: composites vs primes with same residue")
print(f"n mod b^2 = {n % (b*b)}")

targets = [n]  # composite
# Find primes ≡ 91 mod 100
for p in range(91, 2000, 100):
    if p == n:
        continue
    if all(p % i != 0 for i in range(2, int(p**0.5)+1)):
        targets.append(p)
        if len(targets) >= 4:
            break

for t in targets:
    is_prime = all(t % i != 0 for i in range(2, int(t**0.5)+1))
    label = "COMPOSITE" if not is_prime else "prime"
    print(f"\n  {t} ({label}):")
    for ell in range(1, 5):
        g = pow(b, ell, t)
        C = 0
        for r in range(1, t):
            if math.gcd(r, t) != 1:
                continue
            d1 = (b ** ell) * r // t
            gr = g * r % t
            d2 = (b ** ell) * gr // t
            if d1 == d2:
                C += 1
        Q_val = (t - 1) // (b ** ell) if b ** ell <= t else 0
        S = C - Q_val
        m = b ** (ell + 1)
        print(f"    ell={ell}: n mod b^{ell+1} = {t % m:>8}, S = {S:>+4}")
