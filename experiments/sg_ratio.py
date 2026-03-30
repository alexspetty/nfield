#!/usr/bin/env python3
"""
Can we compute S_G at each level independently?

S_G(chi) = sum_{n in G} [chi_bar(n+1) - chi_bar(n)]

G_ell = {n in {0,...,m-1} : floor(n/b^ell) = n mod b}
     = the diagonal set at lag ell

G_1 = {k(b+1) : k = 0,...,b-1}  (for m = b^2)
G_2 = ? (for m = b^3)

The diagonal set at lag ell has b^ell elements
(positions where the ell-th digit equals the 0-th digit
in the base-b expansion).

S_G is computable from the character and the diagonal set.
Both are known. So S_G is computable at every level.

If S_G is known, then |c_hat| / (alpha * |S_G|) = |L(1,chi)|.
We can EXTRACT the L-value at each character at each level.
"""
import cmath, math

b = 5

def compute_SG(base, ell, j, phi, g_gen, dlog, w):
    """Compute S_G(chi_j) at lag ell."""
    m = base ** (ell + 1)
    bl = base ** ell

    # Diagonal set: elements where floor(n/bl) = n mod b
    # i.e., the (ell)-th digit equals the 0th digit
    G = []
    for n_val in range(m):
        high = n_val // bl
        low = n_val % base
        if high == low:
            G.append(n_val)

    # S_G = sum_{n in G} [chi_bar(n+1) - chi_bar(n)]
    SG = 0
    for n_val in G:
        np1 = (n_val + 1) % m
        # chi_bar values
        cb_np1 = w ** (-j * dlog[np1]) if np1 in dlog else 0
        cb_n = w ** (-j * dlog[n_val]) if n_val in dlog else 0
        SG += cb_np1 - cb_n

    return SG

def extract_L_values(n, base, ell):
    """Extract |L(1,chi)| from collision data and S_G."""
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

    # Compute c_hat directly
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

    alpha = m / (math.pi * phi)

    results = []
    for j in range(phi):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue

        ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi
        SG = compute_SG(base, ell, j, phi, g_gen, dlog, w)

        mag_ch = abs(ch)
        mag_SG = abs(SG)

        # |c_hat| = alpha * |L(1,chi)| * |S_G| / phi... no
        # |c_hat| = (1/phi) |B_1| |S_G| and |B_1| = (b/pi)|L(1)|
        # So |L(1)| = |c_hat| * pi * phi / (b^{ell+1} * |S_G|)
        # Wait, alpha = b^{ell+1} / (pi * phi)
        # |c_hat| = alpha * |L(1)| * |S_G|... no
        # c_hat = -B_1 * conj(S_G) / phi
        # |c_hat| = |B_1| * |S_G| / phi
        # |B_1| = (m / pi) |L(1)| ... no, |B_1| = (b/pi)|L(1)| for lag 1
        # More precisely: |B_{1,chi_bar}| = (b^{ell+1}/pi)|L(1,chi)| ... hmm

        # Actually B_1 for characters mod m = b^{ell+1}:
        # |B_1(chi_bar)| depends on the Gauss sum |tau(chi)| = sqrt(m)
        # and L(1,chi) = -pi * i * B_1(chi) / tau(chi_bar)
        # So |B_1| = |tau| * |L(1)| / pi = sqrt(m) * |L(1)| / pi

        if mag_SG > 1e-10:
            L_extracted = mag_ch * phi / (mag_SG)  # = |B_1|
            # Then |L(1)| = |B_1| * pi / sqrt(m)
            L_value = L_extracted * math.pi / math.sqrt(m)
        else:
            L_value = 0

        results.append({
            'j': j, 'c_hat': mag_ch, 'SG': mag_SG,
            'L_value': L_value, 'primitive': True  # TODO check
        })

    return results

n = 91
print(f"n = {n} = 7 x 13, base = {b}\n")

for ell in [1, 2]:
    m = b ** (ell + 1)
    data = extract_L_values(n, b, ell)
    print(f"Lag {ell} (mod {m}): extracted |L(1,chi)|")
    for d in sorted(data, key=lambda x: -x['c_hat'])[:8]:
        print(f"  j={d['j']:>4}: |c_hat|={d['c_hat']:.6f}, "
              f"|S_G|={d['SG']:.4f}, |L(1)|={d['L_value']:.6f}")
    print()

# Now compare: at DIFFERENT lags, the L-values should be
# different (different character families). But characters
# that are lifts of each other should have RELATED L-values.
# The relationship encodes the Euler factors.
