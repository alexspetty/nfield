#!/usr/bin/env python3
"""
The triple collision invariant.

C_2(g) = #{r : floor(br/n) = floor(bgr/n)}         [pairs]
C_3(g) = #{(r,s) : all three of r,gr,s,gs share bin} [triples]

Actually, define:
T(g) = sum_r sum_s [floor(br/n)=floor(bgr/n)=floor(bs/n)=floor(bgs/n)]

This counts ordered pairs (r,s) where both r and s collide
at multiplier g AND r and s are in the same bin.

The Fourier transform:
T_hat(chi) = (1/phi) sum_g T(g) chi_bar(g)

Does T_hat have a closed form in terms of A_d?

T(g) = sum_d #{r in B_d : gr in B_d} * #{s in B_d : gs in B_d}
     = sum_d (C_d(g))^2

where C_d(g) = #{r in B_d cap U(n) : gr mod n in B_d}.

So T = sum_d C_d^2, and the bin-level counts C_d(g) are the
building blocks.

The Fourier transform of C_d(g):
C_d_hat(chi) = (1/phi) sum_g C_d(g) chi_bar(g)
             = (1/phi) sum_g sum_r [r in B_d, gr in B_d] chi_bar(g)

Same substitution s = gr:
= (1/phi) sum_{r in B_d} chi(r) sum_{s in B_d} chi_bar(s)
= (1/phi) A_d(chi) conj(A_d(chi))
= (1/phi) |A_d(chi)|^2

Wait, that's the same as the bin identity again. Each bin's
collision count has the same Fourier structure.

What about T_hat?
T(g) = sum_d C_d(g)^2

T_hat(chi) = sum_d (C_d^2)_hat(chi)

The Fourier transform of C_d^2 is the CONVOLUTION of
C_d_hat with itself. So:

T_hat(chi) = sum_d sum_{chi'} C_d_hat(chi') C_d_hat(chi * chi'^{-1})

This involves cross-character terms. It's NOT just |A_d|^2.
The third moment mixes characters. That's where the phase
information might survive.

Let me compute T_hat directly and see.
"""
import cmath, math

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

g7, g13 = find_gen(7), find_gen(13)
dl7 = {}; v = 1
for k in range(6): dl7[v] = k; v = v * g7 % 7
dl13 = {}; v = 1
for k in range(12): dl13[v] = k; v = v * g13 % 13
w7 = cmath.exp(2j * cmath.pi / 6)
w13 = cmath.exp(2j * cmath.pi / 12)

phi_n = (p-1)*(q-1)

# Compute C_d(g) for each bin d and multiplier g
bins = [set() for _ in range(b)]
for r in range(1, n):
    if math.gcd(r, n) != 1: continue
    d = b * r // n
    bins[d].add(r)

def Cd(d, g):
    return sum(1 for r in bins[d] if (g * r % n) in bins[d])

# T(g) = sum_d Cd(g)^2
def T(g):
    return sum(Cd(d, g)**2 for d in range(b))

# C(g) = sum_d Cd(g)
def C_total(g):
    return sum(Cd(d, g) for d in range(b))

# Compare: C^2 vs T vs C^3
print(f"n = {p} x {q} = {n}\n")
print(f"{'g':>4} {'C(g)':>6} {'C^2':>6} {'T(g)':>6} {'T/C^2':>7}")

for g in range(2, min(n, 30)):
    if math.gcd(g, n) != 1: continue
    c = C_total(g)
    t = T(g)
    ratio = t / c**2 if c > 0 else 0
    print(f"{g:4d} {c:6d} {c**2:6d} {t:6d} {ratio:7.4f}")

# The ratio T/C^2 measures how concentrated the collisions
# are across bins. If all collisions are in one bin: T/C^2 = 1.
# If spread equally: T/C^2 = 1/b.
# The concentration pattern encodes bin-level structure.

print(f"\nMean T/C^2 at composite n={n}: ", end="")
ratios_comp = []
for g in range(2, n):
    if math.gcd(g, n) != 1: continue
    c = C_total(g)
    if c > 0:
        ratios_comp.append(T(g) / c**2)
print(f"{sum(ratios_comp)/len(ratios_comp):.4f}")

# Compare with prime
print(f"\nMean T/C^2 at prime p=97: ", end="")
n2 = 97
bins2 = [set() for _ in range(b)]
for r in range(1, n2):
    d = b * r // n2
    bins2[d].add(r)

def Cd2(d, g):
    return sum(1 for r in bins2[d] if (g * r % n2) in bins2[d])

ratios_prime = []
for g in range(2, n2):
    if math.gcd(g, n2) != 1: continue
    c = sum(Cd2(d, g) for d in range(b))
    t = sum(Cd2(d, g)**2 for d in range(b))
    if c > 0:
        ratios_prime.append(t / c**2)
print(f"{sum(ratios_prime)/len(ratios_prime):.4f}")
