#!/usr/bin/env python3
"""
Test: does the generalized Bernoulli number B_1(chi) factor
through CRT when chi = chi_p x chi_q?

B_1(chi) = (1/n) sum_{a=1}^{n-1} a * chi_bar(a)

For chi = chi_p x chi_q mod pq:
B_1(chi_p x chi_q) = (1/pq) sum_{a coprime to pq} a * chi_p_bar(a) * chi_q_bar(a)

CRT: a <-> (a_p, a_q). Then a = a_q * p * (p^{-1} mod q) + a_p * q * (q^{-1} mod p) mod pq.

Does B_1(chi_p x chi_q) = B_1(chi_p) * B_1(chi_q) * (something)?
"""
import cmath, math

def bernoulli1(n, chi_vals):
    """B_1(chi_bar) = (1/n) sum a * chi_bar(a)"""
    s = 0
    for a in range(1, n):
        if math.gcd(a, n) != 1:
            continue
        s += a * chi_vals[a].conjugate()
    return s / n

def make_chars(p, g):
    """Make all characters mod p using generator g"""
    phi = p - 1
    dlog = {}
    v = 1
    for k in range(phi):
        dlog[v] = k
        v = v * g % p

    chars = []
    w = cmath.exp(2j * cmath.pi / phi)
    for j in range(phi):
        chi = {}
        for a in range(p):
            if math.gcd(a, p) == 1:
                chi[a] = w ** (j * dlog[a])
            else:
                chi[a] = 0
        chars.append(chi)
    return chars

def crt(a_p, a_q, p, q):
    """CRT: find x = a_p mod p, x = a_q mod q, 0 <= x < pq"""
    # Extended gcd to find inverses
    def modinv(a, m):
        g, x, _ = extended_gcd(a, m)
        return x % m

    def extended_gcd(a, b):
        if a == 0:
            return b, 0, 1
        g, x, y = extended_gcd(b % a, a)
        return g, y - (b // a) * x, x

    n = p * q
    return (a_p * q * modinv(q, p) + a_q * p * modinv(p, q)) % n

p, q = 7, 11
n = p * q
b = 10

chars_p = make_chars(p, 3)  # generator 3 mod 7
chars_q = make_chars(q, 2)  # generator 2 mod 11

print(f"n = {p} x {q} = {n}\n")
print(f"B_1 at primes:")

B1_p = []
for j, chi in enumerate(chars_p):
    val = bernoulli1(p, chi)
    B1_p.append(val)
    print(f"  B1(chi_p[{j}]) = {val:.6f}, |B1| = {abs(val):.6f}")

print()
B1_q = []
for j, chi in enumerate(chars_q):
    val = bernoulli1(q, chi)
    B1_q.append(val)
    print(f"  B1(chi_q[{j}]) = {val:.6f}, |B1| = {abs(val):.6f}")

print(f"\nB_1 at composite n={n}:")
print(f"{'j_p':>4} {'j_q':>4} {'|B1_n|':>10} {'|B1_p*B1_q|':>12} {'ratio':>8}")

for jp in range(p-1):
    for jq in range(q-1):
        # Build composite character
        chi_n = {}
        for a in range(n):
            if math.gcd(a, n) == 1:
                chi_n[a] = chars_p[jp][a % p] * chars_q[jq][a % q]
            else:
                chi_n[a] = 0

        B1_n = bernoulli1(n, chi_n)
        product = B1_p[jp] * B1_q[jq]

        if abs(product) > 1e-10:
            ratio = abs(B1_n) / abs(product)
        else:
            ratio = 0

        if abs(B1_n) > 0.001 or abs(product) > 0.001:
            print(f"{jp:4d} {jq:4d} {abs(B1_n):10.6f} {abs(product):12.6f} {ratio:8.4f}")
