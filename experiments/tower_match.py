#!/usr/bin/env python3
"""
Match characters across tower levels and compute the tower ratio.

At lag 1: characters mod 25, phi(25) = 20
At lag 2: characters mod 125, phi(125) = 100
At lag 3: characters mod 625, phi(625) = 500

A character j mod 20 lifts to j, j+20, j+40, j+60, j+80 mod 100.
The original character at level 1 is imprimitive at level 2.
Its lifts include the imprimitive copy plus 4 new primitive chars.

The tower ratio for a lift chi' of chi:
  R = |c_hat_2(chi')| / |c_hat_1(chi)|
encodes the Euler factor and the S_G ratio.
"""
import cmath, math

b = 5
n = 91

def full_data(n, base, ell):
    """Return {j: c_hat} for all odd characters at this lag."""
    m = base ** (ell + 1)
    phi_m = m - m // base  # works for prime base

    units = [a for a in range(1, m) if math.gcd(a, m) == 1]
    phi = len(units)

    # Generator
    g = None
    for c in range(2, m):
        if math.gcd(c, m) != 1: continue
        v, o = 1, 0
        while True:
            v = v * c % m; o += 1
            if v == 1: break
        if o == phi: g = c; break

    dlog = {}
    v = 1
    for k in range(phi):
        dlog[v] = k
        v = v * g % m

    w = cmath.exp(2j * cmath.pi / phi)
    dl_m1 = dlog[m - 1]

    bl = base ** ell
    S = {}
    for p in range(m + 1, 50000):
        if any(p % i == 0 for i in range(2, int(p**0.5)+1)): continue
        if math.gcd(p, base) != 1: continue
        a = p % m
        if a in S: continue
        mult = pow(base, ell, p)
        C = sum(1 for r in range(1, p)
                if bl * r // p == bl * (mult * r % p) // p)
        S[a] = C - (p - 1) // bl

    cls = {}
    for a in units:
        if a not in S: continue
        R = (a - 1) % bl
        if R not in cls: cls[R] = []
        cls[R].append(S[a])

    mean_R = {R: sum(v)/len(v) for R, v in cls.items()}
    Sc = {a: S[a] - mean_R.get((a-1) % bl, 0) for a in units if a in S}

    results = {}
    for j in range(phi):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue
        ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi
        results[j] = ch

    return results, phi

# Compute at each level
data1, phi1 = full_data(n, b, 1)  # mod 25, phi=20
data2, phi2 = full_data(n, b, 2)  # mod 125, phi=100
data3, phi3 = full_data(n, b, 3)  # mod 625, phi=500

print(f"n = {n} = 7 x 13, base = {b}")
print(f"Level 1: {len(data1)} odd chars (phi={phi1})")
print(f"Level 2: {len(data2)} odd chars (phi={phi2})")
print(f"Level 3: {len(data3)} odd chars (phi={phi3})")

# Match: character j at level 1 (mod phi1) lifts to
# j, j+phi1, j+2*phi1, ... at level 2 (mod phi2)
print(f"\nTower ratios (level 1 -> level 2):")
print(f"{'j_1':>4} {'|c1|':>10} {'j_2':>4} {'|c2|':>10} {'ratio':>8} {'lift#':>6}")

for j1 in sorted(data1.keys()):
    c1 = abs(data1[j1])
    if c1 < 1e-8: continue

    for k in range(b):
        j2 = (j1 + k * phi1) % phi2
        if j2 in data2:
            c2 = abs(data2[j2])
            ratio = c2 / c1 if c1 > 1e-8 else 0
            print(f"{j1:4d} {c1:10.6f} {j2:4d} {c2:10.6f} {ratio:8.4f} {k:>6}")

# Now: do the ratios encode factoring information?
# Compare with a prime p' ≡ 91 mod 25
print(f"\n\n=== Same computation for prime p = 191 ≡ 91 mod 25 ===")
n_prime = 191

data1p, _ = full_data(n_prime, b, 1)
data2p, _ = full_data(n_prime, b, 2)

print(f"\nTower ratios for p={n_prime}:")
print(f"{'j_1':>4} {'|c1|':>10} {'j_2':>4} {'|c2|':>10} {'ratio':>8}")

for j1 in sorted(data1p.keys()):
    c1 = abs(data1p[j1])
    if c1 < 1e-8: continue

    for k in range(b):
        j2 = (j1 + k * phi1) % phi2
        if j2 in data2p:
            c2 = abs(data2p[j2])
            ratio = c2 / c1 if c1 > 1e-8 else 0
            print(f"{j1:4d} {c1:10.6f} {j2:4d} {c2:10.6f} {ratio:8.4f}")
