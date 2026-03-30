#!/usr/bin/env python3
"""
The tower: collision data at lags 1, 2, 3 for n = 91 = 7 x 13, base 5.

At lag ell, compute the decomposition theorem at characters mod b^{ell+1}.
Track how |c_hat| changes across lags for related characters.
Extract the tower ratio and see if Euler factors emerge.
"""
import cmath, math

b = 5
n = 91  # 7 x 13

def compute_full_decomposition(n, base, ell):
    """Compute c_hat for all primitive odd chi mod base^{ell+1}."""
    m = base ** (ell + 1)
    if m <= 2:
        return []

    phi_m = m
    for p in set(prime_factors(m)):
        phi_m = phi_m * (p - 1) // p

    units = [a for a in range(1, m) if math.gcd(a, m) == 1]
    phi = len(units)

    # Generator
    g = find_generator(m, phi, units)
    if g is None:
        return []

    dlog = {}
    v = 1
    for k in range(phi):
        dlog[v] = k
        v = v * g % m

    w = cmath.exp(2j * cmath.pi / phi)
    dl_m1 = dlog.get(m - 1, None)
    if dl_m1 is None:
        return []

    # Compute S using primes
    bl = base ** ell  # the multiplier is b^ell
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

    # Center
    cls = {}
    for a in units:
        if a not in S: continue
        R = (a - 1) % bl
        if R not in cls: cls[R] = []
        cls[R].append(S[a])

    if not cls:
        return []

    mean_R = {R: sum(v)/len(v) for R, v in cls.items()}
    Sc = {a: S[a] - mean_R.get((a-1) % bl, 0) for a in units if a in S}

    results = []
    for j in range(phi):
        chi_m1 = w ** (j * dl_m1)
        if abs(chi_m1.real + 1) > 0.01: continue  # odd only

        ch = sum(Sc.get(a, 0) * w ** (-j * dlog[a]) for a in units) / phi

        # Check if primitive: conductor = m, not induced from lower
        # A character mod m is primitive if it's not induced from mod m/p
        # for any prime p | m. For m = b^{ell+1}, the only prime is b.
        # chi is primitive mod m iff it's not constant on cosets of
        # the kernel of reduction mod m/b = b^ell.
        # Test: sum chi over a coset of (1 + b^ell Z/mZ)
        coset_sum = sum(w ** (j * dlog.get((1 + k * base**ell) % m, 0))
                        for k in range(base)
                        if (1 + k * base**ell) % m in dlog)
        is_primitive = abs(coset_sum) < 0.5  # zero for primitive

        results.append({
            'j': j,
            'c_hat': ch,
            'c_hat_mag': abs(ch),
            'primitive': is_primitive,
            'conductor_level': ell + 1 if is_primitive else '?',
        })

    return results

def prime_factors(n):
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def find_generator(m, phi, units):
    for c in range(2, m):
        if math.gcd(c, m) != 1: continue
        v, o = 1, 0
        while True:
            v = v * c % m; o += 1
            if v == 1: break
        if o == phi:
            return c
    return None

print(f"n = {n} = 7 x 13, base = {b}")
print(f"Building the tower...\n")

for ell in range(1, 4):
    m = b ** (ell + 1)
    print(f"=== Lag {ell}, m = {b}^{ell+1} = {m} ===")

    data = compute_full_decomposition(n, b, ell)
    if not data:
        print("  No data (generator not found or too few primes)")
        continue

    prim = [d for d in data if d['primitive']]
    imprim = [d for d in data if not d['primitive']]

    print(f"  {len(data)} odd characters, {len(prim)} primitive, {len(imprim)} imprimitive")

    # Show primitive characters with |c_hat| > 0
    print(f"  Primitive odd characters:")
    for d in sorted(prim, key=lambda x: -x['c_hat_mag']):
        if d['c_hat_mag'] > 1e-6:
            print(f"    j={d['j']:>4}: |c_hat| = {d['c_hat_mag']:.8f}")

    print()
