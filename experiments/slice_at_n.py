#!/usr/bin/env python3
"""
Derive the decomposition at modulus n from first principles.

The collision transform is:
  c_hat_n(chi) = (1/phi(n)) sum_g C(g) chi_bar(g)

Expand C(g) = sum_r [floor(br/n) = floor(bgr/n)]:

  c_hat_n(chi) = (1/phi(n)) sum_r sum_g [same bin] chi_bar(g)

Substitute g = s * r^{-1} where s = gr mod n:
  chi_bar(g) = chi_bar(s * r^{-1}) = chi_bar(s) chi(r)

The condition "same bin" becomes: s in bin_{d(r)}.

  c_hat_n(chi) = (1/phi(n)) sum_r chi(r) sum_{s in bin_d(r)} chi_bar(s)

Define A_d(chi) = sum_{s in bin_d, gcd(s,n)=1} chi(s).
Then sum_{s in bin_d} chi_bar(s) = conj(A_d(chi)).

  c_hat_n(chi) = (1/phi(n)) sum_d conj(A_d(chi)) * A_d(chi)
               = (1/phi(n)) sum_d |A_d(chi)|^2

THIS IS THE IDENTITY. The collision transform is the
sum of squared bin character sums, divided by phi(n).

Let me verify this numerically.
"""
import cmath, math

b = 10
p, q = 7, 13
n = p * q

phi_n = (p-1) * (q-1)

# Build bins
bins = [[] for _ in range(b)]
for r in range(1, n):
    if math.gcd(r, n) != 1:
        continue
    d = b * r // n
    bins[d].append(r)

# Character setup
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

def chi(r, j7, j13):
    if math.gcd(r, n) != 1: return 0
    return w7 ** (j7 * dl7[r % 7]) * w13 ** (j13 * dl13[r % 13])

# Test the identity for several character pairs
print(f"n = {p} x {q} = {n}, base = {b}")
print(f"\nVerifying: c_hat_n(chi) = (1/phi) sum_d |A_d(chi)|^2\n")
print(f"{'j7':>3} {'j13':>4} | {'direct':>12} {'sum |Ad|^2':>12} {'match':>6}")

# Direct computation of c_hat
Q = (n - 1) // b
C = {}
for g_val in range(1, n):
    if math.gcd(g_val, n) != 1: continue
    count = sum(1 for r in range(1, n)
                if math.gcd(r, n) == 1
                and b * r // n == b * (g_val * r % n) // n)
    C[g_val] = count - Q

for j7 in range(6):
    for j13 in range(12):
        # Direct: (1/phi) sum_g S(g) chi_bar(g)
        direct = sum(C[g_val] * chi(g_val, j7, j13).conjugate()
                     for g_val in C) / phi_n

        # Via identity: (1/phi) sum_d |A_d|^2
        # But we need UNCENTERED C(g), not S(g) = C(g) - Q
        # c_hat of C(g) = c_hat of S(g) + Q * delta(chi=trivial)
        # For non-trivial chi, c_hat_C = c_hat_S
        # For trivial chi, c_hat_C = c_hat_S + Q

        # Actually the identity is for C(g) not S(g):
        # (1/phi) sum_g C(g) chi_bar(g) = (1/phi) sum_d |Ad|^2

        direct_C = sum((C[g_val] + Q) * chi(g_val, j7, j13).conjugate()
                       for g_val in C) / phi_n

        # Sum of |A_d|^2
        sum_Ad2 = 0
        for d in range(b):
            Ad = sum(chi(r, j7, j13) for r in bins[d])
            sum_Ad2 += abs(Ad) ** 2
        identity = sum_Ad2 / phi_n

        match = abs(direct_C - identity) < 1e-6
        if abs(direct_C) > 0.01 or abs(identity) > 0.01:
            print(f"{j7:3d} {j13:4d} | {direct_C.real:12.6f} {identity.real:12.6f} "
                  f"{'YES' if match else 'NO':>6}")
