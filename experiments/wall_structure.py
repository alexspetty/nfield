#!/usr/bin/env python3
"""
The wall IS the slice formula. Can we derive s_hat(chi) analytically
from the floor function expansion?

For base 3, mod 9:
S(a) = -1 - floor(a/3) + sum_{n in G} (floor((n+1)a/9) - floor(na/9))
where G = {0, 4, 8} (good slices: floor(n/3) = n mod 3).

The Fourier expansion of floor(ka/m) in terms of a:
floor(ka/m) = ka/m - 1/2 + (1/pi) sum_{j=1}^inf sin(2*pi*j*ka/m) / j

Substituting into the slice formula and taking the collision
transform (Fourier over characters mod 9) should give s_hat
analytically.
"""

import cmath
from math import pi, floor, gcd

b = 3
m = b * b  # 9
G = [n for n in range(m) if floor(n / b) == n % b]  # good slices

print(f"Base {b}, mod {m}")
print(f"Good slices G = {G}")
print(f"|G| = {len(G)} = b^(ell) = {b}")

# Step 1: Verify S(a) from the slice formula
print(f"\nSlice formula: S(a) = -1 - floor(a/{b}) + sum_G (floor((n+1)a/{m}) - floor(na/{m}))")
print()

units = [a for a in range(1, m) if gcd(a, m) == 1]

for a in units:
    # Direct from formula
    S = -1 - floor(a / b)
    for n in G:
        S += floor((n + 1) * a / m) - floor(n * a / m)

    # The linear part (before floor correction)
    S_linear = -1 - a / b
    for n in G:
        S_linear += ((n + 1) * a / m) - (n * a / m)
    # Simplify: sum of ((n+1) - n) * a/m = |G| * a/m
    S_linear_simple = -1 - a / b + len(G) * a / m
    # = -1 - a/3 + 3*a/9 = -1 - a/3 + a/3 = -1

    # The fractional correction
    frac_correction = S - (-1)  # S = -1 + correction from floor

    print(f"  a={a}: S = {S},  linear part = {S_linear_simple:.4f},  correction = {frac_correction}")

print(f"\nThe linear part is ALWAYS -1 (cancels exactly).")
print(f"S(a) = -1 + correction from floor function remainders.")
print(f"The wall structure IS the correction terms.")

# Step 2: Express the correction in terms of fractional parts
print(f"\n{'='*60}")
print(f"The correction terms: {{ka/m}} patterns")
print(f"{'='*60}")

for a in units:
    S = -1 - floor(a / b)
    for n in G:
        S += floor((n + 1) * a / m) - floor(n * a / m)

    # The correction is sum_G (floor((n+1)a/m) - floor(na/m)) - |G|*a/m + a/b
    # = sum_G (floor((n+1)a/m) - floor(na/m) - a/m)
    # = -sum_G {na/m} + sum_G {(n+1)a/m}  ... not quite

    # Actually: floor(x) = x - {x}, so
    # floor((n+1)a/m) - floor(na/m) = a/m - {(n+1)a/m} + {na/m}
    # Sum over G: |G| * a/m + sum_G ({na/m} - {(n+1)a/m})

    frac_sum = 0
    for n in G:
        frac_sum += (n * a % m) / m - ((n + 1) * a % m) / m

    # S = -1 - floor(a/b) + |G|*a/m + frac_sum
    # = -1 - floor(a/b) + a/b + frac_sum  (since |G|/m = 1/b)
    # = -1 + {a/b} + frac_sum  ... hmm

    frac_a_b = (a % b) / b
    S_check = -1 + frac_a_b + frac_sum  # should this work?

    print(f"  a={a}: S={S}, frac_sum={frac_sum:+.4f}, {{a/b}}={frac_a_b:.4f}, "
          f"-1+{{a/b}}+frac_sum={S_check:.4f}")

# Step 3: The collision transform coefficient
print(f"\n{'='*60}")
print(f"Deriving s_hat(chi_1) analytically")
print(f"{'='*60}")

omega = cmath.exp(2j * pi / 6)
gen = 2
dlog = {}
pw = 1
for k in range(6):
    dlog[pw] = k
    pw = (pw * gen) % m

# S values
S_vals = {}
for a in units:
    S = -1 - floor(a / b)
    for n in G:
        S += floor((n + 1) * a / m) - floor(n * a / m)
    S_vals[a] = S

# Class means
cls = {}
for a in units:
    R = (a - 1) % b
    if R not in cls: cls[R] = []
    cls[R].append(S_vals[a])
cls_mean = {R: sum(v)/len(v) for R, v in cls.items()}

S_cent = {a: S_vals[a] - cls_mean[(a-1)%b] for a in units}

# s_hat(chi_1) = (1/6) sum_a S_cent(a) * omega^(-dlog[a])
s_hat = sum(S_cent[a] * omega**(-dlog[a]) for a in units) / 6

print(f"\n  Numerical: s_hat(chi_1) = {s_hat.real:+.6f} {s_hat.imag:+.6f}i")
print(f"  |s_hat| = {abs(s_hat):.6f}")
print(f"  Phase = {cmath.phase(s_hat)/pi:.6f} * pi")

# Can we express this in terms of the good slices and fractional parts?
# s_hat = (1/6) sum_a S_cent(a) * chi_1_bar(a)
# S_cent(a) = S(a) - mean
# S(a) involves floor((n+1)a/9) - floor(na/9) for n in {0, 4, 8}

# The floor difference floor((n+1)a/m) - floor(na/m) equals 1 if
# there's an integer in (na/m, (n+1)a/m], and 0 otherwise.
# This is 1 iff (n+1)a mod m < a (the fractional part wraps).

print(f"\n  Floor difference = 1 iff (n+1)a mod m < a:")
for a in units:
    indicators = []
    for n in G:
        ind = 1 if ((n + 1) * a % m) < a else 0
        indicators.append(ind)
    S_from_ind = -1 - floor(a/b) + sum(indicators)
    print(f"    a={a}: indicators={indicators}, sum={sum(indicators)}, "
          f"-1-floor(a/{b})+sum = {S_from_ind} = S={S_vals[a]}")

print(f"\n  S(a) = -1 - floor(a/b) + #{'{n in G : (n+1)a mod m < a}'}")
print(f"  The wall is a COUNTING FUNCTION: how many good slices")
print(f"  wrap past a multiple of m when scaled by a.")
