#!/usr/bin/env python3
"""
Correct test of decomposition theorem.

S(a) for a in (Z/mZ)* is defined by: pick ANY prime p with
p ≡ a mod m, compute C(b^ell mod p) - floor((p-1)/b).
By finite determination, this depends only on a = p mod m.

The decomposition theorem transforms THIS function S.

For a composite n = pq, the question is different:
n itself has a residue mod m. The collision count C(g)
at the composite uses floor(br/n) for r = 1..n-1.
This is NOT the same as the prime collision invariant
at the residue n mod m.

So the decomposition theorem at composites would need
to define S_composite(g) differently -- as C(g) at the
composite -- and then check if it still decomposes as
-B1 * conj(S_G) / phi.
"""
import cmath, math

def collision_prime(p, b, ell=1):
    """Compute S(p) = C(b^ell mod p) - floor((p-1)/b)."""
    g = pow(b, ell, p)
    C = sum(1 for r in range(1, p) if b * r // p == b * (g * r % p) // p)
    return C - (p - 1) // b

b = 5
m = b * b  # 25
phi = m - m // b  # 20
units = [a for a in range(1, m) if math.gcd(a, m) == 1]

# Populate S(a) using one prime per residue class
S = {}
for p in range(m + 1, 5000):
    if p < 2:
        continue
    if any(p % i == 0 for i in range(2, int(p**0.5) + 1)):
        continue
    if math.gcd(p, b) != 1:
        continue
    a = p % m
    if a not in S:
        S[a] = collision_prime(p, b)

print(f"b = {b}, m = {m}")
print(f"S populated for {len(S)} of {len(units)} residue classes")

# Center
class_sums = {}
class_counts = {}
for a in units:
    if a not in S:
        continue
    R = (a - 1) % b
    class_sums[R] = class_sums.get(R, 0) + S[a]
    class_counts[R] = class_counts.get(R, 0) + 1
class_mean = {R: class_sums[R] / class_counts[R] for R in class_sums}
Sc = {a: S[a] - class_mean[(a-1) % b] for a in units if a in S}

# Generator
g = None
for c in range(2, m):
    if math.gcd(c, m) != 1:
        continue
    v, o = 1, 0
    while True:
        v = v * c % m
        o += 1
        if v == 1:
            break
    if o == phi:
        g = c
        break

dlog = {}
v = 1
for k in range(phi):
    dlog[v] = k
    v = v * g % m

w = cmath.exp(2j * cmath.pi / phi)
dl_m1 = dlog[m - 1]

G = [k * (b + 1) for k in range(b)]

print(f"\nDecomposition theorem test:")
print(f"{'j':>4} {'odd':>4} {'|ĉ|':>10} {'|-B1*SG/φ|':>12} {'ratio':>8}")

for j in range(phi):
    chi_m1 = w ** (j * dl_m1)
    is_odd = abs(chi_m1.real + 1) < 0.01
    if not is_odd:
        continue

    # ĉ
    c_hat = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi

    # B_1
    B1 = sum(a * w ** (-j * dlog[a]) for a in units) / m

    # S_G
    SG = 0
    for nk in G:
        nk1 = (nk + 1) % m
        cb1 = w ** (-j * dlog[nk1]) if nk1 in dlog else 0
        cb0 = w ** (-j * dlog[nk]) if nk in dlog else 0
        SG += cb1 - cb0

    predicted = -B1 * SG.conjugate() / phi

    ratio = abs(c_hat) / abs(predicted) if abs(predicted) > 1e-10 else 0

    print(f"{j:4d} {'odd':>4} {abs(c_hat):10.6f} {abs(predicted):12.6f} {ratio:8.4f}")
