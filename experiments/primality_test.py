#!/usr/bin/env python3
"""
Can the multi-base collision signature distinguish
composite from prime WITHOUT computing C(g)?

S_1(n) at base b depends on n mod b^2. We KNOW n.
So S_1(n) is computable in O(1) from the formula.

Actually: S(a) for a = n mod b^2 is the collision
deviation at any prime p ≡ a mod b^2. We can compute
it from a single prime in that class. But we need
the VALUE of S, not just the residue class.

Wait. By finite determination, S is determined by
the residue class. The decomposition theorem gives
c_hat in terms of B_1 and S_G. Both are computable
from the residue class alone.

So the collision invariant at base b is:
  S = function of (n mod b^2)

And we can compute this function for any n in O(b^2)
time (compute C(g) at a small prime p ≡ n mod b^2).

For the triangulation: compute S at many bases.
Each takes O(b^2). With K bases up to B:
total O(K * B^2) ≈ O(B^3).

The question: does the pattern of S values across
bases distinguish composites from primes?

Actually, the REAL question for the triangulation is
different. It's not primality testing. It's this:

Given n = pq and the L-values from the decomposition
theorem at multiple bases, do the L-values constrain
which (p, q) pairs are possible?
"""
import math, cmath

b_list = [3, 5, 7, 11, 13]

def compute_S_from_residue(a, base):
    """
    S(a) at base b: find a small prime p ≡ a mod b^2
    and compute C(b mod p) - floor((p-1)/b).
    """
    m = base * base
    target = a % m
    # Find smallest prime ≡ target mod m
    for p in range(target if target > 1 else target + m, 100000, m):
        if p < 2:
            continue
        if all(p % i != 0 for i in range(2, int(p**0.5) + 1)):
            g = base % p
            C = sum(1 for r in range(1, p)
                    if base * r // p == base * (g * r % p) // p)
            return C - (p - 1) // base
    return None

# For n = pq, compute S at each base directly
# Then compute what S would be for each candidate (p', q') = n
n = 1763  # 41 x 43

print(f"n = {n}")
print(f"\nL-value data from decomposition theorem at each base:")
print(f"(This is computable from n mod b^2 alone)\n")

for base in b_list:
    if math.gcd(base, n) != 1:
        print(f"  base {base}: shares factor with n")
        continue

    m = base * base
    a = n % m

    S = compute_S_from_residue(a, base)
    print(f"  base {base}: n mod {m} = {a}, S = {S}")

    # What S would be for different factorizations?
    # n = p * q where p*q = 1763
    # Candidate factorizations:
    print(f"    Candidate factorizations and their S at this base:")
    for p_cand in range(2, int(n**0.5) + 1):
        if n % p_cand != 0:
            continue
        q_cand = n // p_cand
        if p_cand > q_cand:
            continue
        # S at the composite depends on n mod b^2, same for all factorizations
        # Because S depends on n, not on p and q separately!
        print(f"      {p_cand} x {q_cand}: S = {S} (same for all factorizations)")

print(f"\n--- Key insight ---")
print(f"S depends on n mod b^2, which is the same regardless of")
print(f"how n factors. The L-values from the decomposition theorem")
print(f"depend on n, not on its factors. Different factorizations")
print(f"of the same n produce IDENTICAL collision data.")
print(f"\nThe triangulation through L-values alone cannot distinguish")
print(f"factorizations because the decomposition theorem is blind")
print(f"to factoring: it operates on n mod b^2, not on (p, q).")
