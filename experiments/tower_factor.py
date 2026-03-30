#!/usr/bin/env python3
"""
Can the tower distinguish WHICH factorization n has?

Compare tower ratios for:
  n = 91 = 7 x 13
  n = 85 = 5 x 17  (can't use, 5 is the base)
  n = 77 = 7 x 11
  n = 119 = 7 x 17
  n = 143 = 11 x 13

All composites, different factorizations.
If tower ratios depend on factorization (not just on n),
the re-composition conjecture has teeth.

But wait: by finite determination, the tower data depends
on n mod b^{ell+1}. Different n values give different data
trivially (different residues). The real test is:

Do two DIFFERENT n values with the same residue mod b^2
(but different factorizations) produce different tower
ratios at lag 2 (where they have different residues mod b^3)?

The answer should be yes (they have different residues mod b^3).
But the question is whether the PATTERN of ratios encodes
the factorization in a way that's extractable.
"""
import cmath, math

b = 5

def direct_tower_ratios(n, ell_low, ell_high):
    """Compute tower ratios from lag ell_low to ell_high."""
    def compute_chat(n, ell):
        m = b ** (ell + 1)
        bl = b ** ell
        phi_m = m - m // b
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

        mult = pow(b, ell, n)

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
            S[a] = total_coll

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

    d_low, phi_low = compute_chat(n, ell_low)
    d_high, phi_high = compute_chat(n, ell_high)

    # Match and compute ratios for top characters
    ratios = {}
    for j1 in sorted(d_low.keys(), key=lambda j: -d_low[j]):
        c1 = d_low[j1]
        if c1 < 1e-8: continue
        lifts = []
        for k in range(b):
            j2 = (j1 + k * phi_low) % phi_high
            if j2 in d_high:
                lifts.append(d_high[j2] / c1)
            else:
                lifts.append(0)
        ratios[j1] = lifts

    return ratios, d_low

# Test composites with different factorizations
composites = [
    (91, "7 x 13"),
    (77, "7 x 11"),
    (119, "7 x 17"),
    (143, "11 x 13"),
    (133, "7 x 19"),
    (187, "11 x 17"),
]

# Also primes for comparison
primes = [
    (89, "prime"),
    (97, "prime"),
    (127, "prime"),
    (131, "prime"),
    (139, "prime"),
    (191, "prime"),
]

print(f"Tower ratios (lag 1 -> lag 2) at base {b}")
print(f"Top character's lift pattern:\n")

for n, label in composites + primes:
    if math.gcd(n, b) != 1:
        continue
    ratios, d_low = direct_tower_ratios(n, 1, 2)
    top_j = max(d_low.keys(), key=lambda j: d_low[j])
    r = ratios[top_j]
    total = sum(r)
    normalized = [x/total if total > 0 else 0 for x in r]

    print(f"  n={n:>4} ({label:>8}): "
          f"ratios = [{', '.join(f'{x:.3f}' for x in r)}]  "
          f"sum={total:.3f}  "
          f"normalized = [{', '.join(f'{x:.2f}' for x in normalized)}]")
