#!/usr/bin/env python3
"""
Compute the collision transform: the Fourier coefficients of S
over Dirichlet characters mod b^2.

S_hat(chi) = (1/phi(b^2)) * sum_{a coprime to b^2} S(a) * chi_bar(a)

Then verify: F° = sum_{chi != chi_0} S_hat(chi) * sum_p chi(p)/p
"""

import cmath
from math import gcd, log, log as ln

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def euler_phi(n):
    result = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result

def primitive_root(n):
    """Find a primitive root mod n (works for n = p^k or 2p^k)."""
    phi = euler_phi(n)
    # Factor phi
    factors = []
    temp = phi
    p = 2
    while p * p <= temp:
        if temp % p == 0:
            factors.append(p)
            while temp % p == 0:
                temp //= p
        p += 1
    if temp > 1:
        factors.append(temp)

    for g in range(2, n):
        if gcd(g, n) != 1:
            continue
        is_root = True
        for f in factors:
            if pow(g, phi // f, n) == 1:
                is_root = False
                break
        if is_root:
            return g
    return None

def dirichlet_characters(n):
    """Generate all Dirichlet characters mod n using primitive root."""
    phi = euler_phi(n)
    g = primitive_root(n)
    if g is None:
        return None

    # Build discrete log table
    dlog = {}
    pw = 1
    for k in range(phi):
        dlog[pw] = k
        pw = (pw * g) % n

    # Characters: chi_j(a) = exp(2*pi*i*j*dlog(a)/phi) for j = 0,...,phi-1
    chars = []
    for j in range(phi):
        def make_chi(j_val):
            def chi(a):
                a_mod = a % n
                if gcd(a_mod, n) != 1:
                    return 0
                return cmath.exp(2j * cmath.pi * j_val * dlog[a_mod] / phi)
            return chi
        chars.append(make_chi(j))

    return chars, dlog, g

# Compute S values for base 10 mod 100
b = 10
bsq = b * b
max_p = 10000

# First, compute S for each residue class mod b^2
S_table = {}
for p in range(b + 2, max_p):
    if not is_prime(p) or p % b == 0:
        continue
    cls = p % bsq
    if cls in S_table:
        continue  # already have this class

    g = pow(b, 1, p)
    C = 0
    for r in range(1, p):
        d_r = b * r // p
        gr = (g * r) % p
        d_gr = b * gr // p
        if d_r == d_gr:
            C += 1
    Q = (p - 1) // b
    S_table[cls] = C - Q

print(f"Collision transform for base {b}, mod {bsq}")
print(f"phi({bsq}) = {euler_phi(bsq)}")
print(f"\nS table (a mod {bsq} -> S):")

coprime_classes = sorted([a for a in range(bsq) if gcd(a, bsq) == 1])
for a in coprime_classes:
    if a in S_table:
        print(f"  S({a:3d}) = {S_table[a]:3d}")

# Compute Dirichlet characters mod b^2
result = dirichlet_characters(bsq)
if result is None:
    print("No primitive root mod", bsq)
    # Use direct character computation for non-cyclic groups
    # For b=10, b^2=100, (Z/100Z)* is not cyclic (it's Z/2 x Z/20)
    print("Group (Z/100Z)* is not cyclic. Using direct computation.")

    # For non-cyclic groups, use CRT: 100 = 4 * 25
    # (Z/4Z)* has phi(4)=2 elements: {1, 3}
    # (Z/25Z)* has phi(25)=20 elements, cyclic with primitive root

    g25 = primitive_root(25)
    print(f"Primitive root mod 25: {g25}")

    # Build characters mod 25
    dlog25 = {}
    pw = 1
    for k in range(20):
        dlog25[pw] = k
        pw = (pw * g25) % 25

    # Characters mod 100 = chars mod 4 x chars mod 25
    # chi_4 has 2 values: trivial (j4=0) and non-trivial (j4=1)
    # chi_25 has 20 values: j25 = 0,...,19

    phi_bsq = euler_phi(bsq)

    # Compute collision transform
    print(f"\nCollision transform coefficients:")
    print(f"{'j4':>3} {'j25':>4} {'Re(S_hat)':>12} {'Im(S_hat)':>12} {'|S_hat|':>10} {'trivial?':>10}")

    for j4 in range(2):
        for j25 in range(20):
            # Compute S_hat = (1/phi) * sum_a S(a) * conj(chi(a))
            s_hat = 0
            for a in coprime_classes:
                if a not in S_table:
                    continue
                # chi(a) = chi_4(a mod 4) * chi_25(a mod 25)
                a4 = a % 4
                a25 = a % 25
                # chi_4: trivial if j4=0, (-1)^dlog if j4=1
                if a4 == 1:
                    chi4 = 1
                elif a4 == 3:
                    chi4 = (-1) ** j4
                else:
                    chi4 = 0
                    continue

                if gcd(a25, 25) != 1:
                    continue
                chi25 = cmath.exp(2j * cmath.pi * j25 * dlog25[a25] / 20)
                chi = chi4 * chi25
                s_hat += S_table[a] * chi.conjugate()

            s_hat /= phi_bsq
            mag = abs(s_hat)
            is_trivial = (j4 == 0 and j25 == 0)

            if mag > 0.001:
                print(f"{j4:3d} {j25:4d} {s_hat.real:12.6f} {s_hat.imag:12.6f} {mag:10.6f} {'TRIVIAL' if is_trivial else ''}")

    # Verify reconstruction
    print(f"\nReconstruction check:")
    print(f"{'a':>4} {'S(a)':>6} {'S_recon':>10}")

    for a in coprime_classes[:10]:
        if a not in S_table:
            continue
        s_recon = 0
        for j4 in range(2):
            for j25 in range(20):
                s_hat = 0
                for aa in coprime_classes:
                    if aa not in S_table:
                        continue
                    a4 = aa % 4
                    a25 = aa % 25
                    if a4 == 1: chi4 = 1
                    elif a4 == 3: chi4 = (-1) ** j4
                    else: continue
                    if gcd(a25, 25) != 1: continue
                    chi25 = cmath.exp(2j * cmath.pi * j25 * dlog25[a25] / 20)
                    chi = chi4 * chi25
                    s_hat += S_table[aa] * chi.conjugate()
                s_hat /= phi_bsq

                # chi(a)
                a4 = a % 4
                a25 = a % 25
                if a4 == 1: chi4_a = 1
                elif a4 == 3: chi4_a = (-1) ** j4
                else: chi4_a = 0
                if gcd(a25, 25) != 1:
                    chi25_a = 0
                else:
                    chi25_a = cmath.exp(2j * cmath.pi * j25 * dlog25[a25] / 20)
                chi_a = chi4_a * chi25_a

                s_recon += s_hat * chi_a

        print(f"{a:4d} {S_table[a]:6d} {s_recon.real:10.4f}")
