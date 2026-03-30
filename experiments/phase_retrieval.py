#!/usr/bin/env python3
"""
Structured phase retrieval for the bin character sums.

We know |A_d|^2 for d = 0,...,b-1 (from the collision transform).
We want arg(A_d) (which encodes the factorization).

The A_d are partial character sums over CONTIGUOUS intervals.
The structural constraint: A_0 + A_1 + ... + A_{b-1} = sum over
all units = 0 (for non-trivial chi). This is one linear constraint
on the complex A_d values.

More constraints come from the contiguity. The bins are adjacent
intervals. Shifting the bin boundary by one residue moves one
term from A_d to A_{d+1}. This means:

  A_d' = A_d - chi(r_boundary)
  A_{d+1}' = A_{d+1} + chi(r_boundary)

The sensitivity of A_d to the bin boundary is chi(r_boundary),
which connects adjacent phases.

Question: given {|A_d|^2} and the constraint sum A_d = 0,
can we recover {A_d} uniquely?

With b magnitudes and 1 linear constraint, we have b+1
real equations for 2b real unknowns (b magnitudes known,
1 real constraint from Re(sum)=0, 1 from Im(sum)=0).
So b+2 equations for 2b unknowns. For b >= 3, underdetermined
by b-2 degrees of freedom.

But the FACTORING constraint adds more: for chi = chi_p x chi_q,
the A_d have structure forced by the CRT grid. Different
factorizations produce different phase patterns. The question
is whether {|A_d|^2} + sum constraint determines the phases
up to a discrete choice that encodes the factorization.
"""
import cmath, math
import numpy as np

b = 10
p, q = 7, 13
n = p * q

def find_gen(prime):
    for c in range(2, prime):
        v, o = 1, 0
        while True:
            v = v * c % prime; o += 1
            if v == 1: break
        if o == prime - 1: return c

g7 = find_gen(7)
g13 = find_gen(13)
dl7 = {}; v = 1
for k in range(6): dl7[v] = k; v = v * g7 % 7
dl13 = {}; v = 1
for k in range(12): dl13[v] = k; v = v * g13 % 13
w7 = cmath.exp(2j * cmath.pi / 6)
w13 = cmath.exp(2j * cmath.pi / 12)

# Compute A_d for a specific character
j7, j13 = 2, 5

bins = [[] for _ in range(b)]
for r in range(1, n):
    if math.gcd(r, n) != 1: continue
    d = b * r // n
    bins[d].append(r)

def chi(r):
    return w7**(j7 * dl7[r%7]) * w13**(j13 * dl13[r%13])

A = []
for d in range(b):
    Ad = sum(chi(r) for r in bins[d])
    A.append(Ad)

print(f"n = {p} x {q} = {n}, chi = ({j7},{j13})")
print(f"\nBin character sums A_d:")
print(f"{'d':>3} {'|A_d|':>8} {'arg(A_d)':>10} {'A_d':>20}")

for d in range(b):
    mag = abs(A[d])
    phase = cmath.phase(A[d])
    print(f"{d:3d} {mag:8.4f} {phase:10.4f} {A[d]:20.4f}")

# Check: sum = 0?
total = sum(A)
print(f"\nSum of A_d = {total:.6f} (should be ~0 for nontrivial chi)")

# The magnitudes (what collision transform gives)
mags = [abs(a) for a in A]
phases = [cmath.phase(a) for a in A]

# Phase differences between adjacent bins
print(f"\nPhase differences (adjacent bins):")
for d in range(b):
    dp = (d + 1) % b
    diff = phases[dp] - phases[d]
    # Normalize to [-pi, pi]
    while diff > math.pi: diff -= 2*math.pi
    while diff < -math.pi: diff += 2*math.pi
    print(f"  arg(A_{dp}) - arg(A_{d}) = {diff:8.4f}")

# Now: how many degrees of freedom?
# We have b=10 complex numbers = 20 real params
# Known: 10 magnitudes = 10 equations
# Constraint: sum = 0 gives 2 equations (real + imag)
# Total: 12 equations for 20 unknowns = 8 DOF
# Global phase is 1 DOF (we can rotate all by same angle)
# So 7 meaningful DOF remain

# But for factoring, we only need to distinguish
# (p,q) = (7,13) from other factorizations of 91.
# 91 = 7 x 13 is the only factorization (semiprime).
# So the question is: do the magnitudes + sum constraint
# distinguish n=91 (composite) from n=91 (if it were prime)?

# Since n=91 is not prime, let's compare with the A_d
# magnitudes at a prime p' near 91
print(f"\n\nComparison: n=91 (composite) vs p=97 (prime)")
print(f"at same character index")

bins_97 = [[] for _ in range(b)]
for r in range(1, 97):
    d = b * r // 97
    bins_97[d].append(r)

# For p=97, characters are mod 97
g97 = find_gen(97)
dl97 = {}; v = 1
for k in range(96): dl97[v] = k; v = v * g97 % 97
w97 = cmath.exp(2j * cmath.pi / 96)

# Use character index j=5 at p=97
j97 = 5
A97 = []
for d in range(b):
    Ad = sum(w97**(j97 * dl97[r]) for r in bins_97[d])
    A97.append(Ad)

print(f"\n{'d':>3} {'|A_91|':>8} {'|A_97|':>8} {'arg_91':>8} {'arg_97':>8}")
for d in range(b):
    print(f"{d:3d} {abs(A[d]):8.4f} {abs(A97[d]):8.4f} "
          f"{cmath.phase(A[d]):8.4f} {cmath.phase(A97[d]):8.4f}")
