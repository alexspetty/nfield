#!/usr/bin/env python3
"""
Derive s_hat(chi) analytically from the slice formula.
The wall = wrapping count. The transform = character sum over wrapping sets.
"""

import cmath
from math import pi, floor, gcd, sqrt

b = 3
m = b * b  # 9
G = [n for n in range(m) if floor(n/b) == n % b]

omega = cmath.exp(2j * pi / 6)
gen = 2
dlog = {}; pw = 1
for k in range(6):
    dlog[pw] = k; pw = (pw * gen) % m

units = [a for a in range(1, m) if gcd(a, m) == 1]

print("ANALYTIC DERIVATION OF THE COLLISION TRANSFORM")
print("="*60)

# For each good slice, compute the wrapping set and its character sum
print(f"\nGood slices G = {G}")
print(f"For each n in G, the wrapping set W_n = {{a : (n+1)a mod {m} < a}}")
print()

for n in G:
    c = n + 1  # the multiplier
    wrap_set = [a for a in units if (c * a % m) < a]
    non_wrap = [a for a in units if (c * a % m) >= a]

    # Character sum over wrapping set
    chi_sum = sum(omega**(-dlog[a]) for a in wrap_set)

    print(f"  n={n}: multiplier c={c}")
    print(f"    Wrapping set: {wrap_set}")
    print(f"    Sum chi_1_bar over wraps: {chi_sum.real:+.4f} {chi_sum.imag:+.4f}i  |sum| = {abs(chi_sum):.4f}")

    if c % m == 0:
        print(f"    (c = {c} ≡ 0 mod {m}: ALL wrap, sum = 0 for non-trivial chi)")
    elif c == 1:
        print(f"    (c = 1: NONE wrap, sum = 0)")

# Analytic decomposition:
# s_hat(chi) = (1/phi) * [-sum_a floor(a/b) chi_bar(a) + sum_n sum_{a in W_n} chi_bar(a)]
# For non-trivial chi, the constant terms (-1 and W_8=all) vanish.

print(f"\n{'='*60}")
print(f"DECOMPOSITION")
print(f"{'='*60}")

# Term 1: -sum floor(a/b) chi_bar(a)
term1 = -sum(floor(a/b) * omega**(-dlog[a]) for a in units)
print(f"\nTerm 1: -Σ floor(a/{b}) χ̄₁(a) = {term1.real:+.6f} {term1.imag:+.6f}i")

# Term 2: sum over non-trivial good slices of character sums over wrapping sets
term2 = 0
for n in G:
    c = n + 1
    if c % m == 0 or c == 1:
        continue  # these contribute 0 to non-trivial characters
    wrap_sum = sum(omega**(-dlog[a]) for a in units if (c * a % m) < a)
    print(f"  Slice n={n} (c={c}): wrap sum = {wrap_sum.real:+.6f} {wrap_sum.imag:+.6f}i")
    term2 += wrap_sum

print(f"\nTerm 2: Σ_{{non-trivial slices}} wrap sums = {term2.real:+.6f} {term2.imag:+.6f}i")

s_hat = (term1 + term2) / 6
print(f"\nŝ(χ₁) = (Term1 + Term2) / φ = {s_hat.real:+.6f} {s_hat.imag:+.6f}i")
print(f"|ŝ| = {abs(s_hat):.6f}")
print(f"Phase = {cmath.phase(s_hat)/pi:.4f}π")

print(f"\n{'='*60}")
print(f"THE WALL IN CLOSED FORM")
print(f"{'='*60}")

# For base 3: only slice n=4 (c=5) contributes.
# c = 5 = 2^(-1) mod 9 (the inverse of the generator)
# The wrapping set {a : 5a mod 9 < a} = {2, 4, 8}
# These are {2^1, 2^2, 2^3} = the first half of the cyclic group

print(f"""
For base 3, only one good slice contributes: n=4, c=5.
  5 = 2⁻¹ mod 9 (inverse of the generator)
  Wrapping set = {{2, 4, 8}} = {{g¹, g², g³}} (first half of cyclic group)

The collision transform coefficient:
  ŝ(χ₁) = (1/6) · [-(−3 + i√3) + (−1 − i√3)]
         = (1/6) · (2 − 2i√3)
         = (1/3)(1 − i√3)
         = (2/3) · e^(−iπ/3)

  |ŝ| = 2/3.  Phase = −π/3.

The 2/3 comes from:
  Term 1 contributes 3/6 = 1/2 (from the floor function)
  Term 2 contributes -1/6 (from the wrapping at the inverse generator)
  The DIFFERENCE is the interference between the floor structure
  and the wrapping structure. 1/2 - 1/6 ... no, the actual
  calculation is more subtle because both terms are complex.

The KEY STRUCTURAL FACT:
  The wrapping set {{2, 4, 8}} is exactly the FIRST HALF of (Z/9Z)*.
  The character sum over the first half of a cyclic group is
  a GAUSS-TYPE SUM.
""")

# Verify: is the wrapping set always a "half group" for prime bases?
print(f"{'='*60}")
print(f"IS THE WRAPPING SET ALWAYS A HALF-GROUP?")
print(f"{'='*60}")

for b in [3, 5, 7]:
    m = b * b
    G = [n for n in range(m) if floor(n/b) == n % b]
    units_b = [a for a in range(1, m) if gcd(a, m) == 1]

    print(f"\nBase {b}, m={m}, |units|={len(units_b)}")
    for n in G:
        c = n + 1
        if c % m == 0 or c == 1:
            continue
        wrap = [a for a in units_b if (c * a % m) < a]
        print(f"  n={n}, c={c}: |wrap|={len(wrap)}, |units|/2={len(units_b)/2:.0f}, "
              f"half? {'YES' if len(wrap) == len(units_b)//2 else 'NO'}")
