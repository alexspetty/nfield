#!/usr/bin/env python3
"""
The antisymmetry S°(a) = -S°(m-a) means F° only sees ODD characters.
Even characters vanish identically.

This is because chi(m-a) = chi(-1)*chi(a), so:
  S°(a)*chi_bar(a) + S°(m-a)*chi_bar(m-a)
  = S°(a)*chi_bar(a) + (-S°(a))*chi_bar(-1)*chi_bar(a)
  = S°(a)*chi_bar(a)*(1 - chi_bar(-1))

For even chi: chi(-1) = 1, so (1 - chi_bar(-1)) = 0. Vanishes.
For odd chi: chi(-1) = -1, so (1 - chi_bar(-1)) = 2. Doubles.

Let's verify: compute s_hat(chi) for each character mod 9
and check which ones vanish.
"""

import cmath
from math import gcd

# Base 3, mod 9
m = 9
gen = 2  # generator of (Z/9Z)*
units = [a for a in range(1, m) if gcd(a, m) == 1]

# S values (from computation)
S = {1: 0, 2: 1, 4: 0, 5: -1, 7: -2, 8: -1}

# Class means
cls = {}
for a in units:
    R = (a - 1) % 3
    if R not in cls:
        cls[R] = []
    cls[R].append(S[a])
cls_mean = {R: sum(v)/len(v) for R, v in cls.items()}

# Centered
S_cent = {a: S[a] - cls_mean[(a-1) % 3] for a in units}

print("S° values:")
for a in units:
    print(f"  S°({a}) = {S_cent[a]:+.4f}    S°({m-a}) = {S_cent[m-a]:+.4f}    sum = {S_cent[a]+S_cent[m-a]:.4f}")

# Discrete log
dlog = {}
pw = 1
for k in range(6):
    dlog[pw] = k
    pw = (pw * gen) % m

# Characters and their parity
print("\nCharacter analysis:")
print(f"{'j':>3} {'chi(-1)':>8} {'parity':>8} {'|s_hat|':>10} {'s_hat':>20}")

for j in range(6):
    # chi_j(a) = exp(2*pi*i*j*dlog[a]/6)
    s_hat = 0
    for a in units:
        phase = 2 * cmath.pi * j * dlog[a] / 6
        chi_bar = cmath.exp(-1j * phase)
        s_hat += S_cent[a] * chi_bar
    s_hat /= len(units)

    # chi(-1) = chi(m-1) = chi(8) = exp(2*pi*i*j*dlog[8]/6) = exp(2*pi*i*j*3/6)
    chi_neg1 = cmath.exp(2j * cmath.pi * j * 3 / 6)
    parity = "even" if abs(chi_neg1.real - 1) < 0.01 else "odd"

    print(f"{j:>3} {chi_neg1.real:>8.1f} {parity:>8} {abs(s_hat):>10.6f} {s_hat.real:>+10.6f}{s_hat.imag:>+10.6f}i")

print("\n=== KEY INSIGHT ===")
print("S°(a) = -S°(m-a) [antisymmetry, proved]")
print("=> s_hat(chi) = 0 for all EVEN characters")
print("=> F°(s) is a sum over ODD characters ONLY")
print("=> The collision transform is blind to even L-functions")
print("=> Only odd L-functions control the penetration depth")
