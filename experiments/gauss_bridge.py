#!/usr/bin/env python3
"""
The Gauss sum bridge: connecting the prime-angle (additive)
framework to the collision transform (multiplicative).

For base 3, mod 9:
- chi_1 is the dominant odd character
- tau(chi_1) = sum_a chi_1(a) * e(a/9) is the Gauss sum
- Does tau relate to 2/3 or to the prime-angle fit?
"""

import cmath
from math import gcd, pi, sqrt

m = 9  # modulus
gen = 2  # generator of (Z/9Z)*
phi = 6

# Build discrete log
dlog = {}
pw = 1
for k in range(phi):
    dlog[pw] = k
    pw = (pw * gen) % m

omega = cmath.exp(2j * pi / phi)
units = sorted(dlog.keys())

print("="*60)
print("THE GAUSS SUM BRIDGE: base 3, mod 9")
print("="*60)

# Character chi_1
print("\nCharacter chi_1 (j=1, order 6, odd):")
for a in units:
    chi = omega ** dlog[a]
    print(f"  chi_1({a}) = {chi.real:+.4f} {chi.imag:+.4f}i")

# Gauss sum tau(chi_1) = sum_a chi_1(a) * e(a/m)
print("\nGauss sum tau(chi_1) = sum_a chi_1(a) * e(a/9):")
tau = 0
for a in units:
    chi = omega ** dlog[a]
    additive = cmath.exp(2j * pi * a / m)
    term = chi * additive
    tau += term
    print(f"  a={a}: chi_1({a}) * e({a}/9) = {term.real:+.6f} {term.imag:+.6f}i")

print(f"\ntau(chi_1) = {tau.real:+.6f} {tau.imag:+.6f}i")
print(f"|tau(chi_1)| = {abs(tau):.6f}")
print(f"sqrt(m) = sqrt(9) = {sqrt(m):.6f}")
print(f"|tau|/sqrt(m) = {abs(tau)/sqrt(m):.6f}")
print(f"|tau|² = {abs(tau)**2:.6f}")
print(f"m = {m}")

# Classical result: |tau(chi)|² = m for primitive characters
print(f"\nCheck: |tau|² = m? {abs(abs(tau)**2 - m) < 0.001}")

# The collision transform coefficient
s_hat = 1/3 - 1j/sqrt(3)  # = (2/3) * e^(-i*pi/3)
print(f"\nCollision transform coefficient:")
print(f"  s_hat(chi_1) = {s_hat.real:+.6f} {s_hat.imag:+.6f}i")
print(f"  |s_hat| = {abs(s_hat):.6f}")

# Is there a relationship between tau and s_hat?
ratio = s_hat / tau
print(f"\nRatio s_hat / tau = {ratio.real:+.6f} {ratio.imag:+.6f}i")
print(f"|ratio| = {abs(ratio):.6f}")

ratio2 = s_hat * tau
print(f"Product s_hat * tau = {ratio2.real:+.6f} {ratio2.imag:+.6f}i")
print(f"|product| = {abs(ratio2):.6f}")

# What about s_hat * conj(tau)?
ratio3 = s_hat * tau.conjugate()
print(f"s_hat * conj(tau) = {ratio3.real:+.6f} {ratio3.imag:+.6f}i")
print(f"|s_hat * conj(tau)| = {abs(ratio3):.6f}")

# The additive phases for primes mod 9
print(f"\n{'='*60}")
print(f"Additive phases e(p/9) for small primes:")
print(f"{'='*60}")

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

# For each class mod 9, show the additive phase
print(f"\n{'class':>6} {'a mod 9':>8} {'e(a/9) angle':>15} {'chi_1(a) angle':>15} {'product angle':>15}")
for a in units:
    add_phase = (2 * pi * a / m) % (2 * pi)
    chi_phase = (2 * pi * dlog[a] / phi) % (2 * pi)
    prod_phase = (add_phase + chi_phase) % (2 * pi)
    print(f"{'':>6} {a:>8} {add_phase/pi:>12.4f}*pi {chi_phase/pi:>12.4f}*pi {prod_phase/pi:>12.4f}*pi")

# The key relationship: does the Gauss sum connect
# the collision transform to the Hurwitz zeta?
print(f"\n{'='*60}")
print(f"L-function via Hurwitz zeta:")
print(f"{'='*60}")
print(f"L(s, chi_1) = (1/tau(chi_1_bar)) * sum_a chi_1_bar(a) * zeta(s, a/9)")
print(f"")
print(f"tau(chi_1_bar) = conj(tau(chi_1)) = {tau.conjugate().real:+.6f} {tau.conjugate().imag:+.6f}i")
print(f"1/tau(chi_1_bar) = {(1/tau.conjugate()).real:+.6f} {(1/tau.conjugate()).imag:+.6f}i")

# The centered sum through the Gauss bridge:
# F°(s) = 2*Re(s_hat * P(s, chi_1))
# P(s, chi_1) = -log L(s, chi_1) + convergent
# L(s, chi_1) = (1/conj(tau)) * sum_a conj(chi_1(a)) * zeta(s, a/9)
#
# So F°(s) = 2*Re(s_hat * (-log[(1/conj(tau)) * sum_a conj(chi_1(a)) * zeta(s, a/9)] + ...))
#
# The Gauss sum enters as a normalization of the L-function.
# It's a constant (doesn't depend on s), so it shifts the phase but not the convergence.

print(f"\nKey insight:")
print(f"  The Gauss sum tau is a CONSTANT (independent of s).")
print(f"  It normalizes the L-function but doesn't affect convergence.")
print(f"  So it can't directly help prove GRH.")
print(f"")
print(f"  BUT: the prime-angle 'fit' measures additive coherence of primes.")
print(f"  The fit at modulus 9 is about how uniformly primes distribute")
print(f"  among the residue classes mod 9.")
print(f"  This uniformity IS Dirichlet's theorem (at s=1).")
print(f"  Below s=1, it becomes a statement about L-function zeros.")
print(f"")
print(f"  The prime-angle fit = additive equidistribution = L-function behavior.")
print(f"  The collision transform = multiplicative equidistribution = same L-functions.")
print(f"  They're the same L-functions seen from opposite sides of the Gauss sum.")

# Compute prime-angle fit for primes mod 9
print(f"\n{'='*60}")
print(f"Prime-angle fit vs collision transform at s = 1/2:")
print(f"{'='*60}")

# Additive character sum at s=1/2
A_sum = 0  # sum_p e(p/9) / sqrt(p)
M_sum = 0  # sum_p chi_1(p) / sqrt(p)

for p in range(5, 100000):
    if not is_prime(p) or p % 3 == 0:
        continue
    a = p % m
    if a not in dlog:
        continue

    # Additive
    A_sum += cmath.exp(2j * pi * a / m) / sqrt(p)

    # Multiplicative
    M_sum += omega ** dlog[a] / sqrt(p)

print(f"  Additive sum:       sum e(p/9)/sqrt(p) = {A_sum.real:+.4f} {A_sum.imag:+.4f}i  |sum| = {abs(A_sum):.4f}")
print(f"  Multiplicative sum: sum chi_1(p)/sqrt(p) = {M_sum.real:+.4f} {M_sum.imag:+.4f}i  |sum| = {abs(M_sum):.4f}")
print(f"")

# Connection via Gauss sum: sum chi(p)/p^s = (1/tau_bar) * sum_a chi_bar(a) * (sum_{p=a mod m} e(a/m)/p^s)?
# No, that's not right. The Gauss sum connects characters to additive characters at the GROUP level,
# not at the prime-sum level.

# But there IS a connection: both sums involve primes in classes mod 9.
# The additive sum splits by class: sum_a e(a/9) * (sum_{p=a} 1/sqrt(p))
# The multiplicative sum splits: sum_a chi_1(a) * (sum_{p=a} 1/sqrt(p))
# Same inner sums! Different outer weights.

# The inner sum for each class
print(f"  Inner sums (sum_{{p=a mod 9}} 1/sqrt(p)):")
class_sums = {}
for a in units:
    class_sums[a] = 0

for p in range(5, 100000):
    if not is_prime(p) or p % 3 == 0:
        continue
    a = p % m
    if a in class_sums:
        class_sums[a] += 1.0 / sqrt(p)

for a in units:
    print(f"    a={a}: {class_sums[a]:.4f}")

# Verify: additive = sum_a e(a/9) * class_sum[a]
A_check = sum(cmath.exp(2j*pi*a/m) * class_sums[a] for a in units)
M_check = sum(omega**dlog[a] * class_sums[a] for a in units)
print(f"\n  Additive sum (reconstructed): {A_check.real:+.4f} {A_check.imag:+.4f}i  matches: {abs(A_sum - A_check) < 0.01}")
print(f"  Multiplicative sum (recon):   {M_check.real:+.4f} {M_check.imag:+.4f}i  matches: {abs(M_sum - M_check) < 0.01}")

print(f"\n  SAME inner sums, different outer weights.")
print(f"  Additive weights: e(a/9)")
print(f"  Multiplicative weights: chi_1(a)")
print(f"  Connected by: chi_1(a) = (1/tau_bar) * sum_b chi_1_bar(b) * e(ab/9)")
