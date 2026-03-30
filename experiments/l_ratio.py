#!/usr/bin/env python3
"""
L-value ratios across tower levels.

Extract |L(1,chi)| at lag 1 and |L(1,chi')| at lag 2
for lifted characters. The ratio L'/L, if it relates
to Euler factors at the factors of n, is the decoder.
"""
import cmath, math

b = 5

def full_extraction(n, base, ell):
    m = base ** (ell + 1)
    bl = base ** ell
    phi_m = m - m // base
    units = [a for a in range(1, m) if math.gcd(a, m) == 1]
    phi = len(units)

    g_gen = None
    for c in range(2, m):
        if math.gcd(c, m) != 1: continue
        v, o = 1, 0
        while True:
            v = v * c % m; o += 1
            if v == 1: break
        if o == phi: g_gen = c; break

    dlog = {}
    v = 1
    for k in range(phi):
        dlog[v] = k
        v = v * g_gen % m

    w = cmath.exp(2j * cmath.pi / phi)
    dl_m1 = dlog[m - 1]

    mult = pow(base, ell, n)

    S_raw = {}
    for a in units:
        total_coll = 0
        for r in range(1, n):
            if math.gcd(r, n) != 1: continue
            if r % m != a: continue
            d1 = bl * r // n
            gr = mult * r % n
            d2 = bl * gr // n
            if d1 == d2:
                total_coll += 1
        S_raw[a] = total_coll

    cls = {}
    for a in units:
        if a not in S_raw: continue
        R = (a - 1) % bl
        if R not in cls: cls[R] = []
        cls[R].append(S_raw[a])
    mean_R = {R: sum(v)/len(v) for R, v in cls.items()} if cls else {}
    Sc = {a: S_raw[a] - mean_R.get((a-1) % bl, 0) for a in units if a in S_raw}

    # Diagonal set
    G = [nv for nv in range(m) if nv // bl == nv % base]

    results = {}
    for j in range(phi):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue

        ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi

        SG = 0
        for nv in G:
            np1 = (nv + 1) % m
            cb1 = w ** (-j * dlog[np1]) if np1 in dlog else 0
            cb0 = w ** (-j * dlog[nv]) if nv in dlog else 0
            SG += cb1 - cb0

        mag_ch = abs(ch)
        mag_SG = abs(SG)

        L_val = mag_ch * phi / mag_SG * math.pi / math.sqrt(m) if mag_SG > 1e-10 else 0

        results[j] = {
            'c_hat': ch, 'mag': mag_ch, 'SG_mag': mag_SG,
            'L': L_val
        }

    return results, phi

n = 91
print(f"n = {n} = 7 x 13, base = {b}\n")

d1, phi1 = full_extraction(n, b, 1)
d2, phi2 = full_extraction(n, b, 2)

print(f"L-value ratios for lifted characters (lag 1 -> lag 2):")
print(f"{'j1':>4} {'L1':>8} | {'j2':>4} {'L2':>8} {'L2/L1':>8} {'lift':>5}")

for j1 in sorted(d1.keys(), key=lambda j: -d1[j]['L']):
    L1 = d1[j1]['L']
    if L1 < 0.01: continue

    for k in range(b):
        j2 = (j1 + k * phi1) % phi2
        if j2 not in d2: continue
        L2 = d2[j2]['L']
        ratio = L2 / L1 if L1 > 1e-10 else 0

        print(f"{j1:4d} {L1:8.4f} | {j2:4d} {L2:8.4f} {ratio:8.4f} {k:5d}")

# Now: do the same for a prime, and compare
print(f"\n\n=== Same for prime p = 191 ===\n")
n2 = 191
d1p, phi1p = full_extraction(n2, b, 1)
d2p, phi2p = full_extraction(n2, b, 2)

print(f"L-value ratios for lifted characters:")
print(f"{'j1':>4} {'L1':>8} | {'j2':>4} {'L2':>8} {'L2/L1':>8} {'lift':>5}")

for j1 in sorted(d1p.keys(), key=lambda j: -d1p[j]['L']):
    L1 = d1p[j1]['L']
    if L1 < 0.01: continue

    for k in range(b):
        j2 = (j1 + k * phi1p) % phi2p
        if j2 not in d2p: continue
        L2 = d2p[j2]['L']
        ratio = L2 / L1 if L1 > 1e-10 else 0

        print(f"{j1:4d} {L1:8.4f} | {j2:4d} {L2:8.4f} {ratio:8.4f} {k:5d}")
