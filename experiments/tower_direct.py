#!/usr/bin/env python3
"""
Direct tower computation: compute c_hat at each lag
by directly evaluating the collision transform at the
specific n, not via proxy primes.
"""
import cmath, math

b = 5

def direct_chat(n, ell):
    """Compute c_hat directly at modulus n, lag ell."""
    m = b ** (ell + 1)
    bl = b ** ell
    phi_m = m
    temp = m
    for p in [b]:  # b is prime
        phi_m = phi_m * (p - 1) // p

    units = [a for a in range(1, m) if math.gcd(a, m) == 1]
    phi = len(units)

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

    # Compute S directly at this n
    mult = pow(b, ell, n)
    S_val = {}
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        a = r % m
        d1 = bl * r // n
        gr = mult * r % n
        d2 = bl * gr // n
        if a not in S_val:
            S_val[a] = 0
        if d1 == d2:
            S_val[a] = S_val.get(a, 0) + 1

    # Normalize: S(a) = total collisions for residues ≡ a mod m,
    # divided by how many such residues exist
    count_a = {}
    for r in range(1, n):
        if math.gcd(r, n) != 1: continue
        a = r % m
        count_a[a] = count_a.get(a, 0) + 1

    # Actually, let me just compute c_hat directly from the
    # full collision deviation
    # S(r) = [floor(bl*r/n) = floor(bl*gr/n)] for each r
    # Then c_hat = (1/phi_n) sum_r S(r) chi_bar(r mod m)

    phi_n = sum(1 for r in range(1, n) if math.gcd(r, n) == 1)

    # But this mixes characters mod m with sums over residues mod n.
    # The finite determination says: S as a function on (Z/mZ)*
    # is the same for all n with the same residue mod m.
    # So let's compute S(a) for a in (Z/mZ)* by averaging over
    # all r ≡ a mod m.

    S = {}
    for a in units:
        total_coll = 0
        total_count = 0
        for r in range(1, n):
            if math.gcd(r, n) != 1: continue
            if r % m != a: continue
            total_count += 1
            d1 = bl * r // n
            gr = mult * r % n
            d2 = bl * gr // n
            if d1 == d2:
                total_coll += 1
        if total_count > 0:
            Q = (n - 1) // bl
            # S(a) = collision rate per residue in class a
            # For finite determination: if all residues in class a
            # have the same collision value, S(a) is that value.
            S[a] = total_coll  # raw count for this class

    # Center
    cls = {}
    for a in units:
        if a not in S: continue
        R = (a - 1) % bl
        if R not in cls: cls[R] = []
        cls[R].append(S[a])

    mean_R = {R: sum(v)/len(v) for R, v in cls.items()} if cls else {}
    Sc = {a: S[a] - mean_R.get((a-1) % bl, 0) for a in units if a in S}

    results = {}
    for j in range(phi):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue
        ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi
        results[j] = abs(ch)

    return results, phi

# Compare composite vs prime
for label, nn in [("91 = 7x13 (composite)", 91), ("191 (prime)", 191)]:
    print(f"\n=== {label} ===")
    for ell in [1, 2]:
        data, phi = direct_chat(nn, ell)
        m = b ** (ell + 1)
        print(f"  Lag {ell} (mod {m}): top 5 |c_hat|:")
        top = sorted(data.items(), key=lambda x: -x[1])[:5]
        for j, mag in top:
            print(f"    j={j:>4}: {mag:.6f}")

    # Tower ratios for lift j -> j+phi1
    d1, phi1 = direct_chat(nn, 1)
    d2, phi2 = direct_chat(nn, 2)
    print(f"  Tower ratios (lag 1 -> lag 2), top characters:")
    for j1 in sorted(d1.keys(), key=lambda j: -d1[j])[:4]:
        c1 = d1[j1]
        if c1 < 1e-6: continue
        ratios = []
        for k in range(b):
            j2 = (j1 + k * phi1) % phi2
            if j2 in d2:
                ratios.append((j2, d2[j2], d2[j2] / c1))
        print(f"    j={j1:>3} (|c1|={c1:.4f}): lifts ->",
              " ".join(f"{r[2]:.3f}" for r in ratios))
