#!/usr/bin/env python3
"""
The A_d as a bilinear form on the CRT grid.

For bin d, A_d(chi_p x chi_q) = sum_{r in bin_d} chi_p(r) chi_q(r)

Via CRT, r <-> (r_p, r_q). The bin bin_d = {r : floor(br/n) = d}
is an interval [dn/b, (d+1)n/b). Under CRT, this interval maps
to a specific region of the p x q grid.

Define the bin matrix M_d with:
  M_d[i][j] = 1 if CRT(i,j) is in bin_d and coprime to n, else 0

Then:
  A_d(chi_p x chi_q) = sum_{i,j} M_d[i][j] chi_p(i) chi_q(j)

This IS a bilinear form: A_d = chi_p^T M_d chi_q_bar
(viewing chi_p and chi_q as vectors).

If M_d has rank 1, A_d factors perfectly.
If M_d has low rank, A_d approximately factors.
The rank of M_d encodes the interleaving complexity.
"""
import math, cmath
import numpy as np

b = 10
p, q = 7, 13
n = p * q

def modinv(a, m):
    g, x = 0, 1
    a0, m0 = a % m, m
    while a0 != 0:
        qq = m0 // a0
        m0, a0 = a0, m0 - qq * a0
        g, x = x, g - qq * x
    return g % m

qi = modinv(q, p)
pi = modinv(p, q)

def crt(rp, rq):
    return (rp * q * qi + rq * p * pi) % n

# Build bin matrices M_d
print(f"n = {p} x {q} = {n}, base = {b}\n")

bin_matrices = []
for d in range(b):
    M = np.zeros((p, q), dtype=int)
    for rp in range(p):
        for rq in range(q):
            r = crt(rp, rq)
            if math.gcd(r, n) != 1:
                continue
            if b * r // n == d:
                M[rp][rq] = 1
    bin_matrices.append(M)

    # Compute rank via SVD
    U, sigma, Vt = np.linalg.svd(M.astype(float))
    rank = np.sum(sigma > 1e-10)
    total = np.sum(M)

    # How close to rank 1?
    if sigma[0] > 1e-10:
        rank1_approx = sigma[0]**2 / np.sum(sigma**2)
    else:
        rank1_approx = 0

    print(f"Bin {d}: {total:>2} elements, rank = {rank}, "
          f"rank-1 fraction = {rank1_approx:.4f}")

    # Show the matrix
    if d < 3:  # just first few
        print(f"  M_{d} (rows = r_p, cols = r_q):")
        for rp in range(p):
            row = "  " + "".join(str(M[rp][rq]) for rq in range(q))
            print(row)
        print()

# Now: verify A_d = chi_p^T M_d chi_q
print(f"\nVerification: A_d = chi_p^T M_d chi_q_bar")

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

# Test a specific character pair
j7, j13 = 2, 5
print(f"\nTest chi_p[{j7}] x chi_q[{j13}]:")

for d in range(b):
    # Direct A_d
    Ad_direct = 0
    for r in range(1, n):
        if math.gcd(r, n) != 1: continue
        if b * r // n != d: continue
        chi_val = w7**(j7 * dl7[r%7]) * w13**(j13 * dl13[r%13])
        Ad_direct += chi_val

    # Via matrix: chi_p^T M_d chi_q_bar
    chi_p_vec = np.array([w7**(j7 * dl7[i]) if i in dl7 else 0
                          for i in range(p)], dtype=complex)
    chi_q_vec = np.array([w13**(j13 * dl13[j]) if j in dl13 else 0
                          for j in range(q)], dtype=complex)

    M = bin_matrices[d].astype(complex)
    Ad_matrix = chi_p_vec @ M @ chi_q_vec.conj()

    match = abs(Ad_direct - Ad_matrix) < 1e-8
    print(f"  d={d}: direct={Ad_direct:.4f}, matrix={Ad_matrix:.4f}, "
          f"{'YES' if match else 'NO'}")

# THE KEY: what are the singular values of M_d?
print(f"\nSingular value structure of bin matrices:")
for d in range(b):
    M = bin_matrices[d].astype(float)
    sigma = np.linalg.svd(M, compute_uv=False)
    nonzero = sigma[sigma > 1e-10]
    if len(nonzero) > 0:
        print(f"  d={d}: sigma = [{', '.join(f'{s:.3f}' for s in nonzero[:5])}]"
              f"{'...' if len(nonzero) > 5 else ''}")
