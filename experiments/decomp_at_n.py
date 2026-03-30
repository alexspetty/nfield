#!/usr/bin/env python3
"""
THE KEY COMPUTATION: does the decomposition theorem hold
at modulus n itself, with characters mod n?

At modulus m = b^2, the decomposition theorem says:
  s_hat(chi) = -B_1(chi_bar) * conj(S_G(chi)) / phi(m)

where G = {k in {0,...,m-1} : floor(k/b) = k mod b}.

At modulus m = n (the composite itself), what is:
1. The diagonal set G_n?
2. S_G at the composite?
3. Does s_hat = -B_1 * conj(S_G) / phi(n)?

The slice formula for the collision invariant at modulus n:
S(a) = C(a) - floor((n-1)/b) where C(a) counts collisions
of floor(br/n) under multiplication by a.

The Fourier transform:
s_hat_n(chi) = (1/phi(n)) sum_{a coprime to n} S(a) chi_bar(a)

The decomposition theorem prediction:
s_hat_n(chi) = -B_1(chi_bar, n) * conj(S_G_n(chi)) / phi(n)

where B_1(chi_bar, n) = (1/n) sum_{a=1}^{n-1} a chi_bar(a)
and S_G_n(chi) = sum_{k in G_n} [chi_bar(k+1) - chi_bar(k)]

What is G_n? For the standard decomposition theorem, G is
the set of "slice boundaries" where the digit changes.
At modulus m = b^2: G = {k(b+1) : k = 0,...,b-1}.
At modulus m = n: floor(br/n) changes when br crosses a
multiple of n. The slice boundaries are at r = kn/b for
k = 0,...,b-1. In residues mod n, these are at...

Actually, the slice formula says:
S(a) = -1 - floor(a/b) + sum_{k in G} d_k(a)
where d_k(a) = floor((k+1)a/n) - floor(ka/n)
and G = {k : floor(k/b) = k mod b} when working mod b^2.

But for the decomposition at modulus n with characters mod n,
the slice formula has a DIFFERENT form. The digit function
floor(br/n) for r = 1,...,n-1 has b slices. The collision
under multiplication by a counts how many r have the same
digit as ar mod n.

Let me just compute everything directly and test whether
the decomposition theorem holds.
"""
import cmath, math

b = 10
p, q = 7, 13
n = p * q  # 91

phi_n = (p-1) * (q-1)  # 72

# Step 1: Compute S(a) for all a coprime to n
def collision_count(n, base, a):
    C = 0
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        d1 = base * r // n
        ar = a * r % n
        d2 = base * ar // n
        if d1 == d2:
            C += 1
    return C

Q = sum(1 for r in range(1, n) if math.gcd(r, n) == 1) // b
# Actually Q = floor((n-1)/b) for the standard definition
Q_std = (n - 1) // b  # = 9

S = {}
for a in range(1, n):
    if math.gcd(a, n) != 1:
        continue
    S[a] = collision_count(n, b, a) - Q_std

# Step 2: Compute s_hat_n(chi) directly
# Characters mod n = characters mod 7 x characters mod 13
# Need generators for (Z/7Z)* and (Z/13Z)*
def find_gen(prime):
    for c in range(2, prime):
        v, o = 1, 0
        while True:
            v = v * c % prime; o += 1
            if v == 1: break
        if o == prime - 1:
            return c

g7 = find_gen(7)   # 3
g13 = find_gen(13)  # 2

dl7 = {}; v = 1
for k in range(6):
    dl7[v] = k; v = v * g7 % 7

dl13 = {}; v = 1
for k in range(12):
    dl13[v] = k; v = v * g13 % 13

w7 = cmath.exp(2j * cmath.pi / 6)
w13 = cmath.exp(2j * cmath.pi / 12)

# s_hat_n(j7, j13) = (1/phi_n) sum_a S(a) chi_bar(a)
# chi(a) = w7^(j7 * dl7[a%7]) * w13^(j13 * dl13[a%13])

print(f"n = {p} x {q} = {n}, base = {b}")
print(f"\nTransform 2: s_hat_n(chi_p x chi_q)\n")

# Step 3: Compute B_1 and S_G at modulus n, and test decomposition
# B_1(chi_bar) = (1/n) sum_{a coprime to n} a * chi_bar(a)

# What is S_G at modulus n? The "diagonal set" at modulus n
# for the digit function floor(br/n) with b bins:
# G = {k : the slice at k contributes to collisions}
# In the standard decomposition, G at modulus m is where
# floor(k/b) = k mod b. But modulus is m = b^2 there.
#
# For modulus n, the slice formula is:
# S(a) = sum_k d_k(a) - (some baseline)
# where the sum is over the "slices" of the digit function.
# The slices are: for digit d, bin_d = {r : floor(br/n) = d}
# Each bin has ~n/b elements.
# A collision at (r, ar) means r and ar are in the same bin.

# Let me try: define G_n as the set of "boundary residues"
# where the digit function transitions.
# floor(br/n) changes value at r = ceil(d*n/b) for d=1,...,b-1.
# The boundary residues are: r_d = ceil(d*n/b) for d=1,...,b-1
# In {0,...,n-1}: the boundaries are at d*n/b.

# Actually for the decomposition theorem proof, the "good slices"
# G are the values n in {0,...,m-1} such that the digit
# d_n(a) = floor((n+1)a/m) - floor(na/m) contributes.
# At m = b^2, these are the "diagonal" values.
# At m = n, these would be... all values? Or specific ones?

# Let me just test the decomposition directly by computing
# both sides and comparing.

print(f"{'j7':>3} {'j13':>4} | {'|s_hat|':>10} {'|B1*SG/phi|':>12} {'ratio':>8}")

for j7 in range(6):
    for j13 in range(12):
        # Compute s_hat directly
        sh = 0
        for a in S:
            a7 = a % 7
            a13 = a % 13
            chi_bar = (w7 ** (-j7 * dl7[a7])) * (w13 ** (-j13 * dl13[a13]))
            sh += S[a] * chi_bar
        sh /= phi_n

        # Compute B_1
        B1 = 0
        for a in range(1, n):
            if math.gcd(a, n) != 1:
                continue
            a7 = a % 7
            a13 = a % 13
            chi_bar = (w7 ** (-j7 * dl7[a7])) * (w13 ** (-j13 * dl13[a13]))
            B1 += a * chi_bar
        B1 /= n

        # For S_G: try G = bin boundaries
        # Boundaries at k*n/b for k = 0,...,b
        # The residues just below each boundary
        G_n = []
        for d in range(b):
            boundary = d * n // b
            if 0 <= boundary < n:
                G_n.append(boundary)

        SG = 0
        for k in G_n:
            k1 = (k + 1) % n
            cb1 = 0
            cb0 = 0
            if math.gcd(k1, n) == 1:
                cb1 = (w7 ** (-j7 * dl7[k1 % 7])) * (w13 ** (-j13 * dl13[k1 % 13]))
            if math.gcd(k, n) == 1:
                cb0 = (w7 ** (-j7 * dl7[k % 7])) * (w13 ** (-j13 * dl13[k % 13]))
            SG += cb1 - cb0

        predicted = -B1 * SG.conjugate() / phi_n

        if abs(sh) > 0.001 or abs(predicted) > 0.001:
            ratio = abs(sh) / abs(predicted) if abs(predicted) > 1e-10 else 0
            print(f"{j7:3d} {j13:4d} | {abs(sh):10.6f} {abs(predicted):12.6f} {ratio:8.4f}")
