#!/usr/bin/env python3
"""
Euler factor stripping: the re-composition test.

At base b, the decomposition theorem gives:
  |c_hat(chi)| = (b / pi*phi) |L(1,chi)| |S_G(chi)|

L(1,chi) = prod_l (1 - chi(l)/l)^{-1}

For a candidate factor p' of n:
  L(1,chi) = (1 - chi(p')/p')^{-1} * L_stripped(1,chi)

where L_stripped has the Euler factor at p' removed.

If p' is actually a factor of n, then L_stripped is the
same whether we strip at p' or at q' = n/p'. The stripped
L-values should satisfy a CONSISTENCY condition across
characters and bases.

The test: for each candidate p', compute
  R(chi, p') = |c_hat(chi)| * |1 - chi(p')/p'|

This "re-composes" the L-value by removing the Euler
factor at p'. For the CORRECT p', R should have specific
structure. For wrong p', it should not.

What structure? The Euler factor at q = n/p' is still
present. So R = (b/pi*phi) |L_stripped * (1-chi(q)/q)^{-1}| |S_G|.
The key: for the correct (p,q), stripping BOTH Euler factors
gives L_doubly_stripped, which has NO dependence on the
factorization. It depends only on the character and on primes
other than p and q.

So: R2(chi, p', q') = |c_hat| * |1-chi(p')/p'| * |1-chi(q')/q'|
For the correct (p',q'), R2 should be smooth and consistent
across bases. For wrong (p',q'), it won't be.
"""
import cmath, math

def make_chars(base):
    m = base * base
    phi_m = m - m // base
    units = [a for a in range(1, m) if math.gcd(a, m) == 1]

    g = None
    for c in range(2, m):
        if math.gcd(c, m) != 1: continue
        v, o = 1, 0
        while True:
            v = v * c % m; o += 1
            if v == 1: break
        if o == phi_m: g = c; break

    dlog = {}
    v = 1
    for k in range(phi_m):
        dlog[v] = k
        v = v * g % m

    w = cmath.exp(2j * cmath.pi / phi_m)
    dl_m1 = dlog.get(m - 1, 0)

    chars = []
    for j in range(phi_m):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue  # odd only

        chi = {}
        for a in units:
            chi[a] = w ** (j * dlog[a])
        chars.append((j, chi))

    return chars, units, m, phi_m, dlog, w

def compute_chat(n, base):
    m = base * base
    phi_m = m - m // base
    units = [a for a in range(1, m) if math.gcd(a, m) == 1]

    g = None
    for c in range(2, m):
        if math.gcd(c, m) != 1: continue
        v, o = 1, 0
        while True:
            v = v * c % m; o += 1
            if v == 1: break
        if o == phi_m: g = c; break

    dlog = {}
    v = 1
    for k in range(phi_m):
        dlog[v] = k
        v = v * g % m

    w = cmath.exp(2j * cmath.pi / phi_m)
    dl_m1 = dlog.get(m - 1, 0)

    # Get S values
    S = {}
    for p in range(m + 1, 30000):
        if any(p % i == 0 for i in range(2, int(p**0.5)+1)): continue
        if math.gcd(p, base) != 1: continue
        a = p % m
        if a in S: continue
        mult = base % p
        C = sum(1 for r in range(1, p)
                if base * r // p == base * (mult * r % p) // p)
        S[a] = C - (p-1) // base

    cls = {}
    for a in units:
        if a not in S: continue
        R = (a - 1) % base
        if R not in cls: cls[R] = []
        cls[R].append(S[a])
    mean_R = {R: sum(v)/len(v) for R, v in cls.items()}
    Sc = {a: S[a] - mean_R[(a-1) % base] for a in units if a in S}

    results = []
    for j in range(phi_m):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue

        ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi_m

        # Also need chi(p') for candidate factors
        chi_vals = {a: w ** (j * dlog[a]) for a in units}

        results.append({
            'j': j,
            'c_hat': ch,
            'chi_vals': chi_vals,
        })

    return results

# Test the Euler stripping
p_true, q_true = 41, 43
n = p_true * q_true

base = 7  # Use base 7 for clear data
m = base * base

print(f"n = {p_true} x {q_true} = {n}, base = {base}, m = {m}")

data = compute_chat(n, base)

# For each candidate factor p', compute the consistency score
print(f"\nEuler stripping test:")
print(f"{'p_cand':>7} {'q_cand':>7} {'mean_R2':>10} {'std_R2':>10} {'score':>8}")

candidates = list(range(2, int(n**0.5) + 2))

for p_cand in candidates:
    if n % p_cand == 0:
        q_cand = n // p_cand
    else:
        q_cand = n // p_cand  # Not exact, but test anyway

    # For each character, compute R2 = |c_hat| * |1 - chi(p')/p'| * |1 - chi(q')/q'|
    R2_values = []
    for d in data:
        ch = d['c_hat']
        chi = d['chi_vals']

        p_mod = p_cand % m
        q_mod = q_cand % m

        if p_mod in chi and q_mod in chi:
            euler_p = abs(1 - chi[p_mod] / p_cand)
            euler_q = abs(1 - chi[q_mod] / q_cand)
            R2 = abs(ch) * euler_p * euler_q
            if R2 > 1e-10:
                R2_values.append(R2)

    if len(R2_values) < 3:
        continue

    mean_R2 = sum(R2_values) / len(R2_values)
    std_R2 = (sum((v - mean_R2)**2 for v in R2_values) / len(R2_values)) ** 0.5
    cv = std_R2 / mean_R2 if mean_R2 > 0 else 999

    is_factor = (n % p_cand == 0)
    marker = " **" if is_factor else ""
    if is_factor or cv < 0.5:
        print(f"{p_cand:7d} {n // p_cand:7d} {mean_R2:10.6f} {std_R2:10.6f} {cv:8.4f}{marker}")
