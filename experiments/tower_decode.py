#!/usr/bin/env python3
"""
The decoder: given tower ratios, can we predict them
from a candidate factorization?

The tower ratio R = |c_hat_{ell+1}(chi')| / |c_hat_ell(chi)|

By the decomposition theorem at each level:
  |c_hat_ell| = (b^{ell+1} / pi*phi_ell) |L(1,chi)| |S_G_ell|
  |c_hat_{ell+1}| = (b^{ell+2} / pi*phi_{ell+1}) |L(1,chi')| |S_G_{ell+1}|

For a lift chi' of chi:
  L(1, chi') = L(1, chi) * E(chi', b)
where E is the Euler correction from the conductor change.

For primitive chi mod b^{ell+1}, chi' mod b^{ell+2}:
  If chi' is also primitive (conductor b^{ell+2}):
    L(1, chi') = L(1, chi) (same underlying L-function,
    just evaluated at a different character that happens
    to have the same L-function when both are primitive)

Actually wait. A primitive character mod b^2 and a
primitive character mod b^3 are DIFFERENT characters
with DIFFERENT L-functions. The lift relationship is:

chi' mod b^3 restricts to chi mod b^2 means
chi'(a) = chi(a) for a coprime to b.

But L(1, chi') != L(1, chi) in general. They're
different Dirichlet L-functions.

The relationship is:
  L(s, chi') = L(s, chi) if chi' is induced from chi
  L(s, chi') is new if chi' is primitive with higher conductor

For the lift: among the b lifts of chi to mod b^3,
one is induced (imprimitive) and b-1 are new (primitive).
The imprimitive lift has L(s, chi') = L(s, chi) * (1 - chi(b)/b^s).
The primitive lifts have genuinely new L-functions.

So the tower ratio for the IMPRIMITIVE lift is:
  R_imprim = (alpha ratio) * |1 - chi(b)/b| * |S_G_2| / |S_G_1|

And for primitive lifts, R involves new L-values.

The imprimitive lift is the one we can predict!
Let me compute it.
"""
import cmath, math

b = 5

def full_tower_data(n, base, ell):
    """Return character data at lag ell including chi values."""
    m = base ** (ell + 1)
    bl = base ** ell
    phi_m = m - m // base
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

    mult = pow(base, ell, n)

    S = {}
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
        S[a] = total_coll

    cls = {}
    for a in units:
        if a not in S: continue
        R = (a - 1) % bl
        if R not in cls: cls[R] = []
        cls[R].append(S[a])

    mean_R = {R: sum(v)/len(v) for R, v in cls.items()} if cls else {}
    Sc = {a: S[a] - mean_R.get((a-1) % bl, 0) for a in units if a in S}

    # Compute c_hat AND chi(b) for each odd character
    results = {}
    for j in range(phi):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue

        ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi

        # chi(b) = w^(j * dlog[b]) if b is a unit mod m
        b_mod = base % m
        chi_b = w ** (j * dlog[b_mod]) if b_mod in dlog else 0

        # Check primitivity via coset sum
        coset_sum = sum(w ** (j * dlog.get((1 + k * base**ell) % m, 0))
                        for k in range(base)
                        if (1 + k * base**ell) % m in dlog)
        is_prim = abs(coset_sum) < 0.5

        results[j] = {
            'c_hat': ch,
            'mag': abs(ch),
            'chi_b': chi_b,
            'primitive': is_prim,
        }

    return results, phi

# Compute at n=91, base 5
n = 91
print(f"n = {n} = 7 x 13, base = {b}\n")

d1, phi1 = full_tower_data(n, b, 1)  # mod 25
d2, phi2 = full_tower_data(n, b, 2)  # mod 125

# For each character at level 1, identify which lift at level 2
# is imprimitive (induced from level 1)
print(f"Imprimitive lifts and Euler factor test:")
print(f"{'j1':>4} {'|c1|':>8} {'j2_imp':>6} {'|c2_imp|':>8} "
      f"{'ratio':>8} {'predicted':>10} {'match':>6}")

alpha_ratio = (b**3 / (b**3 - b**2)) / (b**2 / (b**2 - b))
# = (b^3 / phi(b^3)) / (b^2 / phi(b^2))
# = (b^3 / (b^3-b^2)) / (b^2 / (b^2-b))
# = (b/(b-1)) / (b/(b-1)) = 1... no

# Actually: alpha_ell = b^{ell+1} / (pi * phi(b^{ell+1}))
# alpha_1 = b^2 / (pi * phi(b^2)) = 25 / (pi * 20) = 25/(20*pi)
# alpha_2 = b^3 / (pi * phi(b^3)) = 125 / (pi * 100) = 125/(100*pi)
# ratio = (125/100) / (25/20) = 1.25 / 1.25 = 1.0
alpha_r = 1.0  # the alpha ratio is always 1 for prime base b

for j1 in sorted(d1.keys(), key=lambda j: -d1[j]['mag']):
    if d1[j1]['mag'] < 0.01: continue

    c1 = d1[j1]['mag']
    chi_b = d1[j1]['chi_b']

    # The imprimitive lift at level 2: the character that
    # restricts to chi at level 1. This is the lift with
    # index j1 (same index, mod phi2)
    # Actually for imprimitive: j2 = j1 * (phi2/phi1) ... no
    # The imprimitive character at level 2 with index j1
    # maps a -> chi(a mod b^2) which has index j1 when
    # viewed mod phi1. At level 2, this is index j1 * (phi2/phi1)...

    # The imprimitive lift should be detectable: it's the one
    # at level 2 that is NOT primitive.

    # Among the b lifts j1, j1+phi1, ..., j1+(b-1)*phi1,
    # find the imprimitive one
    imp_j2 = None
    for k in range(b):
        j2 = (j1 + k * phi1) % phi2
        if j2 in d2 and not d2[j2]['primitive']:
            imp_j2 = j2
            break

    if imp_j2 is None:
        # All lifts are primitive, or the imprimitive one
        # has c_hat = 0
        # The imprimitive lift at level 2 has c_hat = 0
        # because imprimitive odd characters have c_hat = 0
        # by the antisymmetry argument!
        # This is what we proved in Paper C!
        print(f"{j1:4d} {c1:8.4f}   (imprimitive lift has c_hat = 0)")
        continue

    c2_imp = d2[imp_j2]['mag']
    ratio = c2_imp / c1 if c1 > 0 else 0

    # Predicted ratio for imprimitive lift:
    # c_hat_2(imprim) = 0 (by antisymmetry/centering)
    # OR
    # The Euler factor |1 - chi(b)/b|
    euler = abs(1 - chi_b / b)
    predicted = alpha_r * euler  # * S_G ratio (unknown)

    print(f"{j1:4d} {c1:8.4f} {imp_j2:6d} {c2_imp:8.4f} "
          f"{ratio:8.4f} {predicted:10.4f}")
