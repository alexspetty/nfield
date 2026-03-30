#!/usr/bin/env python3
"""
Decompose P into signal (correlated with B1) and noise.

P = Σ_{k=1}^{b-1} chi_bar(k)
B1 = (1/m) Σ_a a chi_bar(a)

We proved: m*B1 = b * Σ_k Σ_j j chi_bar(k+jb)
(from the coset decomposition with coset sums = 0)

The j=0 slice contributes nothing to B1 (j=0 terms vanish).
The j=1,...,b-1 slices contribute everything.

But P comes entirely from the j=0 slice.

So P and B1 draw from DIFFERENT slices. Their correlation
comes from the character's structure linking different slices.

Key insight: chi_bar(k+jb) = chi_bar(k) * chi_bar(1+jb/k)
           = chi_bar(k) * psi(j*k^{-1} mod b)

where psi is the fine-subgroup character.

So: m*B1 = b * Σ_k chi_bar(k) * Σ_j j psi(j*k^{-1})
         = b * Σ_k chi_bar(k) * F(k)

where F(k) = Σ_j j psi(j*k^{-1} mod b).

Now psi(l) = omega^l for some primitive b-th root omega.
F(k) = Σ_{j=0}^{b-1} j * omega^{j*k^{-1} mod b}

Since k^{-1} mod b just permutes the exponents:
F(k) = Σ_{l=0}^{b-1} (l*k mod b) * omega^l

Hmm, this is (l*k mod b), not l*k. Let me be more careful.

j*k^{-1} mod b: as j runs 0..b-1, this is a permutation.
Let l = j*k^{-1} mod b, so j = l*k mod b.

F(k) = Σ_l (l*k mod b) * omega^l

Now l*k mod b = l*k - b*floor(l*k/b). So:

F(k) = k * Σ_l l * omega^l - b * Σ_l floor(l*k/b) * omega^l
     = k * F0 - b * G(k)

where F0 = Σ l omega^l = b/(omega-1) (computed earlier)
and G(k) = Σ_l floor(l*k/b) * omega^l.

So: m*B1 = b * Σ_k chi_bar(k) * [k*F0 - b*G(k)]
         = b*F0 * Σ_k k*chi_bar(k) - b^2 * Σ_k chi_bar(k)*G(k)
         = b*F0*Q - b^2 * Σ_k chi_bar(k)*G(k)

where Q = Σ k chi_bar(k).

The first term: b*F0*Q links B1 to Q (the weighted partial sum).
The second term: couples P to G(k) (the floor-function sum).

The signal in P correlated with B1 comes through Q (which is
a weighted version of P). The noise comes from the G(k) coupling.

Let me compute G(k) for base 5 to see its structure.
"""
import cmath, math

b = 5
m = b * b
omega = cmath.exp(2j * cmath.pi / b)  # primitive b-th root

print(f"Base {b}, omega = e^(2*pi*i/{b})")
print(f"|F0| = b/|omega-1| = {b/abs(omega-1):.4f}")
print(f"F0 = {b/(omega-1):.4f}")

F0 = sum(l * omega**l for l in range(b))
print(f"F0 (direct) = {F0:.4f}")

# G(k) = sum_l floor(l*k/b) * omega^l for k=1..b-1
print(f"\nG(k) for k=1..{b-1}:")
for k in range(1, b):
    G = sum(((l*k)//b) * omega**l for l in range(b))
    print(f"  G({k}) = {G:.4f}, |G| = {abs(G):.4f}")

# The key ratio: |G(k)| / |F0|
print(f"\n|G(k)|/|F0|:")
for k in range(1, b):
    G = sum(((l*k)//b) * omega**l for l in range(b))
    print(f"  k={k}: {abs(G)/abs(F0):.4f}")

# The coupling: Σ chi_bar(k)*G(k) / P
# If G(k) is approximately constant * chi_bar(k)^{-1},
# then the sum would be proportional to P.
# Let's check.
print(f"\nG(k) structure:")
for k in range(1, b):
    G = sum(((l*k)//b) * omega**l for l in range(b))
    print(f"  k={k}: floor values = {[(l*k)//b for l in range(b)]}")

# At base 5: floor(l*k/5) for l=0..4, k=1..4:
# k=1: [0,0,0,0,0] -> G = 0
# k=2: [0,0,0,1,1] -> G = 3*w^3 + 4*w^4 (wait, floor(0)=0,floor(2/5)=0,floor(4/5)=0,floor(6/5)=1,floor(8/5)=1)
# Actually: l*k = l*2, floor(l*2/5) for l=0..4: 0,0,0,1,1
# G(2) = 0 + 0 + 0 + 1*w^3 + 1*w^4

print("\nDirect computation:")
for k in range(1, b):
    terms = []
    for l in range(b):
        f = (l*k) // b
        terms.append(f"  l={l}: lk={l*k}, floor={f}")
    G = sum(((l*k)//b) * omega**l for l in range(b))
    print(f"k={k}: G={G:.4f}")
    for t in terms:
        print(t)

# KEY: for k=1, floor(l*1/b) = 0 for all l < b. So G(1) = 0!
# For k=b-1=4, floor(l*4/5): 0,0,1,2,3. G(4) = w^2 + 2w^3 + 3w^4.
# The G(k) values depend on the Beatty-type partition of l*k by b.

# The signal: b*F0*Q. The noise: b^2 * Σ chi(k)*G(k).
# At base 5, we know the total ratio P/B1 = sqrt(5)/2.
# Let's verify the decomposition.

print(f"\n\nVerification for base 5, j=1:")
dlog = {1:0, 2:1, 3:7, 4:2, 6:8, 7:5, 8:3, 9:14, 11:16, 12:9,
        13:19, 14:6, 16:4, 17:13, 18:15, 19:18, 21:12, 22:17, 23:11, 24:10}

w20 = cmath.exp(2j * cmath.pi / 20)  # primitive 20th root
j = 1  # first odd character

# chi_bar(k) for k=1..4
chi_bar = {k: w20**(-j*dlog[k]) for k in range(1,5)}

P = sum(chi_bar[k] for k in range(1,5))
Q = sum(k * chi_bar[k] for k in range(1,5))
B1_full = sum(a * w20**(-j*dlog[a]) for a in dlog) / m

# Fine subgroup character: psi(l) = chi(1+l*b)
psi_vals = {}
for l in range(b):
    elem = (1 + l*b) % m
    if elem in dlog:
        psi_vals[l] = w20**(-j*dlog[elem])
    else:
        psi_vals[l] = 0

omega_fine = psi_vals[1] / psi_vals[0]  # should be a b-th root of unity
print(f"Fine character: psi(1) = {psi_vals[1]:.4f}")
print(f"omega_fine = {omega_fine:.4f}")
print(f"|omega_fine| = {abs(omega_fine):.4f}")

F0_fine = sum(l * psi_vals[l] for l in range(b))
print(f"F0 (fine) = {F0_fine:.4f}")

# G(k) using fine character
for k in range(1, b):
    G = sum(((l*k)//b) * psi_vals[l] for l in range(b))
    print(f"G({k}) = {G:.6f}")

# Verify: m*B1 = b*F0*Q - b^2 * Σ chi_bar(k)*G(k)
coupling = sum(chi_bar[k] * sum(((l*k)//b) * psi_vals[l] for l in range(b))
               for k in range(1, b))
rhs = b * F0_fine * Q - b*b * coupling
print(f"\nm*B1 = {m * B1_full:.6f}")
print(f"b*F0*Q - b^2*coupling = {rhs:.6f}")
print(f"Match: {abs(m*B1_full - rhs) < 1e-6}")
