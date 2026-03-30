#!/usr/bin/env python3
"""
Prove s_hat = B1 * S_G / phi by expanding the slice formula.

s_hat(chi) = (1/phi) sum_a S_centered(a) chi_bar(a)

S(a) = -1 + {a/b} + sum_{n in G} [{na/m} - {(n+1)a/m}]

Each fractional part sum:
sum_a {ka/m} chi_bar(a) = ???

Let's compute both sides symbolically for base 5.
"""
import cmath, math

b = 5
m = b * b  # 25
phi = 20  # phi(25)
PI = math.pi

# Discrete logs for generator g=2
dlog = {1:0, 2:1, 3:7, 4:2, 6:8, 7:5, 8:3, 9:14, 11:16, 12:9,
        13:19, 14:6, 16:4, 17:13, 18:15, 19:18, 21:12, 22:17, 23:11, 24:10}

units = sorted(dlog.keys())
w = cmath.exp(2j * PI / phi)

# Good slices
G = [k * (b+1) for k in range(b)]  # 0, 6, 12, 18, 24
print(f"Good slices: {G}")

# Build S table
S = {}
for p in range(m+1, 50000):
    if p < 2: continue
    is_p = True
    if p % 2 == 0 or p % 3 == 0:
        is_p = (p == 2 or p == 3)
    else:
        i = 5
        while i*i <= p:
            if p%i==0 or p%(i+2)==0: is_p=False; break
            i += 6
    if not is_p or math.gcd(p, b) != 1: continue
    a = p % m
    if a in S: continue
    C = sum(1 for r in range(1, p) if b*r//p == b*(b*r%p)//p)
    S[a] = C - (p-1)//b

# Class means
from collections import defaultdict
cls = defaultdict(list)
for a in units:
    if a in S: cls[(a-1)%b].append(S[a])
mean_R = {R: sum(v)/len(v) for R, v in cls.items()}

# Centered S
Sc = {a: S[a] - mean_R[(a-1)%b] for a in units if a in S}

# For j=1 (first odd character), verify term by term

j = 1

# LHS: s_hat = (1/phi) sum Sc(a) chi_bar(a)
lhs = sum(Sc[a] * w**(-j*dlog[a]) for a in units if a in Sc) / phi

# RHS: B1(chi_bar) * S_G(chi) / phi
# B1(chi_bar) = (1/m) sum a chi_bar(a)
B1 = sum(a * w**(-j*dlog[a]) for a in units) / m

# S_G(chi) = sum_{n in G} [chi_bar(n+1) - chi_bar(n)]
S_G = 0
for n in G:
    n1 = (n + 1) % m
    n_mod = n % m
    v_n1 = w**(-j*dlog[n1]) if n1 in dlog else 0
    v_n = w**(-j*dlog[n_mod]) if n_mod in dlog and n_mod > 0 else 0
    S_G += v_n1 - v_n

rhs = B1 * S_G / phi

print(f"\nj={j}:")
print(f"  LHS (s_hat)     = {lhs}")
print(f"  RHS (B1*SG/phi) = {rhs}")
print(f"  Match: {abs(lhs - rhs) < 1e-10}")

# Now: derive WHY this is true.
#
# s_hat = (1/phi) sum_a Sc(a) chi_bar(a)
#       = (1/phi) sum_a [S(a) - mean_R] chi_bar(a)
#       = (1/phi) sum_a S(a) chi_bar(a)  - (1/phi) sum_a mean_R chi_bar(a)
#
# The centering term: mean_R depends on (a-1) mod b, so it splits
# into b groups. For non-trivial chi, each group's chi_bar sum
# may not vanish (it depends on chi's restriction to the b classes).
#
# Let's compute both parts:

# Uncenterered: (1/phi) sum S(a) chi_bar(a)
uncent = sum(S[a] * w**(-j*dlog[a]) for a in units if a in S) / phi

# Centering correction: (1/phi) sum mean_R[(a-1)%b] chi_bar(a)
cent_corr = sum(mean_R[(a-1)%b] * w**(-j*dlog[a]) for a in units) / phi

print(f"\n  Uncentered s_hat = {uncent}")
print(f"  Centering corr   = {cent_corr}")
print(f"  Centered s_hat   = {uncent - cent_corr}")
print(f"  Should equal LHS: {abs(lhs - (uncent - cent_corr)) < 1e-10}")

# Now decompose the uncentered part using the slice formula:
# S(a) = -1 + {a/b} + sum_{n in G} [{na/m} - {(n+1)a/m}]

# Term 1: sum (-1) chi_bar(a) = -sum chi_bar(a) = 0 (non-trivial chi)
term1 = sum(-1 * w**(-j*dlog[a]) for a in units)
print(f"\n  Term1 (-1 sum): {term1} (should be ~0)")

# Term 2: sum {a/b} chi_bar(a)
term2 = sum((a/b - a//b) * w**(-j*dlog[a]) for a in units)
print(f"  Term2 ({{a/b}}): {term2}")

# Term 3: sum_{n in G} sum_a [{na/m} - {(n+1)a/m}] chi_bar(a)
term3 = 0
for n in G:
    for a in units:
        na_frac = (n*a % m) / m  # {na/m}
        n1a_frac = ((n+1)*a % m) / m  # {(n+1)a/m}
        term3 += (na_frac - n1a_frac) * w**(-j*dlog[a])
print(f"  Term3 (frac parts): {term3}")

print(f"\n  Sum terms / phi = {(term1 + term2 + term3) / phi}")
print(f"  Uncentered s_hat = {uncent}")
print(f"  Match: {abs((term1+term2+term3)/phi - uncent) < 1e-8}")

# Now: the key identity. For each n in G:
# sum_a {na/m} chi_bar(a) = ???
#
# Classical: for primitive chi mod m, gcd(n,m)=1:
# sum_{a coprime} chi_bar(a) {na/m} = -chi(n) * tau(chi_bar) * B1(chi_bar) / ???
#
# Let's just compute it:
print(f"\n  Fractional part sums by n:")
for n in G:
    if n == 0:
        # {0*a/m} = 0 for all a
        s = 0
    else:
        s = sum((n*a%m)/m * w**(-j*dlog[a]) for a in units)
    s_over_B1 = s / B1 if abs(B1) > 1e-10 else 0
    chi_n = w**(j*dlog[n%m]) if n%m in dlog and n%m > 0 else 0
    print(f"    n={n:3d}: sum={s:.4f}, sum/B1={s_over_B1:.4f}, chi(n)={chi_n:.4f}")
