#!/usr/bin/env python3
"""
Can we isolate the Euler factors at p=7 and q=13 from
the tower data?

Strategy: compute L(1, chi) two ways:
1. From the collision data (extracted via decomposition theorem)
2. From the Euler product directly (requires knowing primes)

Then: L_extracted / L_without_p_q = Euler_factor_at_p * Euler_factor_at_q

If we can compute L_without_p_q cheaply (it's the L-function
with two Euler factors removed), we can isolate the product
of Euler factors at p and q. That product constrains (p, q).

But computing L_without_p_q requires knowing p and q.

ALTERNATIVE: compute L(1, chi) from the Euler product with
ALL primes, and compare with the extracted value. They should
match. Then systematically REMOVE one Euler factor at a time
for each candidate prime p', and see which removal makes the
extracted values match a modified Euler product.

Actually simpler: the extracted |L(1,chi)| IS the full
L-value. We can also compute it from the Euler product
using known primes. They should agree. The question is
whether there's useful information in comparing the two
computations.

EVEN SIMPLER: at two different tower levels, we have
L-values at characters of different conductors. The
ratio L(1,chi')/L(1,chi) for a lift involves the
conductor change. For characters that are related by
the Hecke operator at b, the ratio is controlled by
the eigenvalue of the Hecke operator, which depends on
the arithmetic of n at b.

Let me just compute everything and see what structure
emerges.
"""
import cmath, math

b = 5
p_true, q_true = 7, 13
n = p_true * q_true

def L_value_euler(chi_func, modulus, num_terms=1000):
    """Compute L(1, chi) via Euler product over small primes."""
    result = 1.0 + 0j
    for p in range(2, num_terms):
        if any(p % i == 0 for i in range(2, int(p**0.5)+1)):
            continue
        if p == 0:
            continue
        chi_p = chi_func(p % modulus)
        factor = 1.0 / (1.0 - chi_p / p)
        result *= factor
    return result

def L_value_stripped(chi_func, modulus, strip_primes, num_terms=1000):
    """L(1,chi) with Euler factors at strip_primes removed."""
    result = 1.0 + 0j
    for p in range(2, num_terms):
        if any(p % i == 0 for i in range(2, int(p**0.5)+1)):
            continue
        if p in strip_primes:
            continue
        chi_p = chi_func(p % modulus)
        factor = 1.0 / (1.0 - chi_p / p)
        result *= factor
    return result

# Build characters mod 25
m = 25
phi = 20
units = [a for a in range(1, m) if math.gcd(a, m) == 1]

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

print(f"n = {n} = {p_true} x {q_true}, base = {b}, m = {m}\n")

# For each odd character mod 25:
print(f"{'j':>4} {'|L_euler|':>10} {'|L_extract|':>12} "
      f"{'|L_no_7|':>10} {'|L_no_13|':>10} {'|L_no_7_13|':>12} "
      f"{'E7':>8} {'E13':>8} {'E7*E13':>8}")

# First get extracted L-values from collision data
bl = b
mult = b % n
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
mean_R = {R: sum(v)/len(v) for R, v in cls.items()}
Sc = {a: S_raw[a] - mean_R.get((a-1) % bl, 0) for a in units if a in S_raw}

G = [k * (b + 1) for k in range(b)]

for j in range(phi):
    chi_m1 = w ** (j * dl_m1)
    if abs(chi_m1.real + 1) > 0.01: continue

    # Character function
    def chi_func(a, j=j):
        if a % m in dlog:
            return w ** (j * dlog[a % m])
        return 0

    # Extracted L-value
    ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi
    SG = sum((w ** (-j * dlog[(nv+1)%m]) if (nv+1)%m in dlog else 0)
             - (w ** (-j * dlog[nv]) if nv in dlog else 0) for nv in G)
    L_extract = abs(ch) * phi / abs(SG) * math.pi / math.sqrt(m) if abs(SG) > 1e-10 else 0

    # Euler product L-values
    L_full = L_value_euler(chi_func, m)
    L_no_7 = L_value_stripped(chi_func, m, {7})
    L_no_13 = L_value_stripped(chi_func, m, {13})
    L_no_7_13 = L_value_stripped(chi_func, m, {7, 13})

    # Euler factors
    chi_7 = chi_func(7)
    chi_13 = chi_func(13)
    E7 = abs(1 / (1 - chi_7 / 7))
    E13 = abs(1 / (1 - chi_13 / 13))

    print(f"{j:4d} {abs(L_full):10.6f} {L_extract:12.6f} "
          f"{abs(L_no_7):10.6f} {abs(L_no_13):10.6f} {abs(L_no_7_13):12.6f} "
          f"{E7:8.4f} {E13:8.4f} {E7*E13:8.4f}")

print(f"\nKey: E7 = |1/(1-chi(7)/7)|, E13 = |1/(1-chi(13)/13)|")
print(f"If we know L_extract and L_no_7_13, then E7*E13 = L_extract / L_no_7_13")
print(f"But computing L_no_7_13 requires knowing 7 and 13.")
print(f"\nThe question: can we get E7*E13 from the TOWER data")
print(f"(multiple levels) without computing L_no_7_13?")
