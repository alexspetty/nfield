#!/usr/bin/env python3
"""
Triangulation: do L-values at multiple bases jointly
constrain the factorization?

For n = pq, the decomposition theorem at base b gives
|c_hat(chi)| = (b / pi*phi) |L(1,chi)| |S_G(chi)|
for primitive odd chi mod b^2.

The values depend on n mod b^2. For different bases b1, b2,
the character families are different. The L-values are at
different moduli.

Question: given the collision data at bases b1 and b2,
can we narrow down the factorization of n?

Approach: for candidate factorizations n = p'*q' with
p'*q' = n, compute what the collision invariant WOULD be
at each base, and check consistency with the actual data.

If n is prime, there's only one "factorization" (n itself).
If n = pq, the collision data should be consistent with
n = pq but inconsistent with n being prime.
"""
import cmath, math

def collision_invariant_at_base(n, base):
    """Compute S(a) for a = n mod base^2, at multiplier base."""
    g = base % n
    if g == 0:
        return None
    C = 0
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        if base * r // n == base * (g * r % n) // n:
            C += 1
    Q = (n - 1) // base
    return C - Q

def multi_base_signature(n, bases):
    """Collision invariant at multiple bases."""
    sig = []
    for b in bases:
        if math.gcd(b, n) != 1:
            sig.append(None)
        else:
            sig.append(collision_invariant_at_base(n, b))
    return sig

# Test: can multi-base signature distinguish n=pq from primes?
bases = [3, 7, 11, 13, 17, 19, 23]

# Target composite
p, q = 41, 43
n = p * q  # 1763

print(f"Target: n = {p} x {q} = {n}")
print(f"Bases: {bases}")

sig_n = multi_base_signature(n, bases)
print(f"\nSignature of n={n}: {sig_n}")

# Find primes near n and compute their signatures
print(f"\nSignatures of nearby primes:")
nearby_primes = []
for candidate in range(n - 20, n + 20):
    if candidate < 2:
        continue
    if all(candidate % i != 0 for i in range(2, int(candidate**0.5) + 1)):
        nearby_primes.append(candidate)

for p_test in nearby_primes[:8]:
    sig = multi_base_signature(p_test, bases)
    # Distance from n's signature
    dist = sum((a - b_val)**2 for a, b_val in zip(sig_n, sig)
               if a is not None and b_val is not None)
    match = all(a == b_val for a, b_val in zip(sig_n, sig)
                if a is not None and b_val is not None)
    print(f"  p={p_test}: sig={sig}  dist={dist:>6}  match={'YES' if match else 'no'}")

# Now: for a composite, what determines the signature?
# sig at base b depends on n mod b^2.
# For n = 1763: n mod 9 = 7, n mod 49 = 0 (7|1763!), etc.
print(f"\nResidues of n={n}:")
for b in bases:
    m = b * b
    print(f"  n mod {b}^2 = n mod {m} = {n % m}")
    # Also check if b divides n
    if n % b == 0:
        print(f"    ** {b} divides {n} = {n//b} x {b} **")

# The triangulation: n mod b^2 for many b's gives
# n mod lcm(b1^2, b2^2, ...) by CRT.
# How much of n does this determine?
from functools import reduce
def lcm(a, b):
    return a * b // math.gcd(a, b)

moduli = [b*b for b in bases if math.gcd(b, n) == 1]
combined = reduce(lcm, moduli)
print(f"\nCombined modulus (LCM of b^2 for coprime bases): {combined}")
print(f"n mod combined = {n % combined}")
print(f"Bits of n determined: {math.log2(combined):.1f} out of {math.log2(n):.1f}")
