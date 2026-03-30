#!/usr/bin/env python3
"""
The re-composition theorem: can L-value data at multiple
bases jointly constrain the factorization?

At base b, the decomposition theorem gives:
  |c_hat(chi)| * pi * phi / b = |L(1,chi)| * |S_G(chi)|

for primitive odd chi mod b^2.

The LEFT side is computable from n mod b^2.
The RIGHT side factors into L-value and geometry.

At two different bases b1, b2: the L-values are at
different character moduli (b1^2 and b2^2). But for
n = pq, there might be RELATIONSHIPS between L-values
at different moduli that depend on the factorization.

Key idea: L(1, chi) for chi mod b^2 can be expressed as
a product over primes. The Euler factor at p is
(1 - chi(p)/p)^{-1}. For n = pq, the Euler factors at
p and q are special because chi(p) and chi(q) depend on
n's factors.

At base b with gcd(b, n) = 1: chi mod b^2 is evaluated
at p and q. The value chi(p) depends on p mod b^2, which
we know (p mod b^2 is determined by n and q, but we don't
know q).

HOWEVER: across multiple bases, the Euler factor
constraints might overdetermine p.

Specifically: at base b, for chi mod b^2,
  L(1, chi) = prod_{primes l} (1 - chi(l)/l)^{-1}

The Euler factor at l = p is (1 - chi(p)/p)^{-1}.
Since chi is mod b^2, chi(p) = chi(p mod b^2).

We know n = pq but not p. For a candidate p', the Euler
factor would be (1 - chi(p')/p')^{-1}. The collision
data constrains |L(1,chi)| * |S_G|. If we can isolate
the Euler factor at p, the correct p' gives consistent
data across all bases while wrong p' values don't.
"""
import cmath, math

def modinv(a, m):
    g, x = 0, 1
    a0, m0 = a % m, m
    while a0 != 0:
        q = m0 // a0
        m0, a0 = a0, m0 - q * a0
        g, x = x, g - q * x
    return g % m

def make_chars_and_data(n, base):
    """At base b, compute |c_hat(chi)| for primitive odd chi mod b^2."""
    m = base * base
    phi_m = m - m // base  # phi(b^2) for prime b

    units = [a for a in range(1, m) if math.gcd(a, m) == 1]

    # Generator
    g = None
    for c in range(2, m):
        if math.gcd(c, m) != 1: continue
        v, o = 1, 0
        while True:
            v = v * c % m; o += 1
            if v == 1: break
        if o == phi_m: g = c; break

    if g is None:
        return []

    dlog = {}
    v = 1
    for k in range(phi_m):
        dlog[v] = k
        v = v * g % m

    w = cmath.exp(2j * cmath.pi / phi_m)
    dl_m1 = dlog[m - 1]

    # Compute S(a) for all units, using a prime p ≡ a mod m
    S = {}
    for p in range(m + 1, 50000):
        if any(p % i == 0 for i in range(2, int(p**0.5)+1)): continue
        if math.gcd(p, base) != 1: continue
        a = p % m
        if a in S: continue
        mult = base % p
        C = sum(1 for r in range(1, p)
                if base * r // p == base * (mult * r % p) // p)
        S[a] = C - (p-1) // base

    # Center
    cls = {}
    for a in units:
        if a not in S: continue
        R = (a - 1) % base
        if R not in cls: cls[R] = []
        cls[R].append(S[a])
    mean_R = {R: sum(v)/len(v) for R, v in cls.items()}
    Sc = {a: S[a] - mean_R[(a-1) % base] for a in units if a in S}

    # Compute c_hat for odd characters
    results = []
    for j in range(phi_m):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue  # odd only

        ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi_m
        mag = abs(ch)

        # Also compute chi(n) and chi at small primes
        chi_at_n = w ** (j * dlog[n % m]) if (n % m) in dlog else 0

        results.append({
            'j': j,
            'c_hat_mag': mag,
            'chi_at_n': chi_at_n,
        })

    return results

# Test
p_true, q_true = 41, 43
n = p_true * q_true

bases = [3, 5, 7, 11, 13]

print(f"n = {p_true} x {q_true} = {n}")
print(f"\nCollision spectral data at each base:")

for base in bases:
    if not all(base % i != 0 for i in range(2, int(base**0.5)+1)):
        continue
    if math.gcd(base, n) != 1:
        print(f"\nBase {base}: shares factor with n")
        continue

    data = make_chars_and_data(n, base)
    if not data:
        continue

    print(f"\nBase {base} (m = {base**2}):")
    # Sum of |c_hat|^2 (Parseval)
    parseval = sum(d['c_hat_mag']**2 for d in data)
    print(f"  {len(data)} odd characters, Parseval sum = {parseval:.4f}")

    # The c_hat values encode |L(1,chi)| * |S_G(chi)|
    # For each candidate factorization p' * q' = n,
    # we can compute what the Euler factors at p' would be
    print(f"  Top 3 |c_hat| values:")
    data.sort(key=lambda d: -d['c_hat_mag'])
    for d in data[:3]:
        print(f"    j={d['j']:>3}: |c_hat| = {d['c_hat_mag']:.6f}")
