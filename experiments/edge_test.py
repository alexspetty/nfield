#!/usr/bin/env python3
"""
Does |s_hat(chi)| correlate with |Re(chi(b-1))|?
If so, the large coefficients are determined by the edge of the
Beatty partition, and the anti-correlation with |P| follows from
the primes not concentrating at the edge.
"""
from math import gcd, pi, cos, sin, sqrt
from collections import defaultdict

b = 10
m = b * b

# Build S, center
S_table = {}
for p in range(m+1, 50000):
    if p < 2: continue
    if any(p % i == 0 for i in range(2, int(p**0.5)+1)): continue
    if gcd(p, b) != 1: continue
    a = p % m
    if a in S_table: continue
    C = sum(1 for r in range(1, p) if b*r//p == b*(b*r%p)//p)
    S_table[a] = C - (p-1)//b

units = [a for a in range(1, m) if gcd(a, m) == 1]
phi = len(units)
cls = defaultdict(list)
for a in units:
    if a in S_table: cls[(a-1)%b].append(S_table[a])
mean_R = {R: sum(v)/len(v) for R, v in cls.items()}
S_cent = {a: S_table[a] - mean_R[(a-1)%b] for a in units if a in S_table}

# Characters
g25 = 2
dlog25 = {}
val = 1
for i in range(20):
    dlog25[val] = i
    val = val * g25 % 25
dlog4 = {1: 0, 3: 1}

print(f"{'j':>2} {'k':>3} {'|sh|':>7} {'Re(chi9)':>9} {'|Re|':>6} "
      f"{'|P|':>7} {'Re(sh*P)':>10}")

data = []
for j in range(2):
    for k in range(20):
        chi = {}
        for a in range(100):
            if gcd(a, 100) != 1:
                chi[a] = 0
            else:
                angle = pi*j*dlog4[a%4] + 2*pi*k*dlog25[a%25]/20
                chi[a] = complex(cos(angle), sin(angle))
        if abs(chi[99] - (-1)) > 1e-6: continue

        s_hat = sum(S_cent.get(a,0) * chi[a].conjugate() for a in units) / phi

        # chi(9) = chi(b-1)
        chi9 = chi[9]
        re_chi9 = chi9.real

        # P(0.5)
        P = complex(0)
        for p in range(m+1, 2000000):
            if p < 2: continue
            if any(p % i == 0 for i in range(2, int(p**0.5)+1)): continue
            if gcd(p, b) != 1: continue
            P += chi[p % m] * p**(-0.5)

        prod = s_hat * P
        data.append((abs(s_hat), abs(re_chi9), abs(P), prod.real))

        print(f"{j:>2} {k:>3} {abs(s_hat):>7.4f} {re_chi9:>+9.4f} "
              f"{abs(re_chi9):>6.4f} {abs(P):>7.4f} {prod.real:>+10.4f}")

# Correlations
n = len(data)
sh = [d[0] for d in data]
rchi = [d[1] for d in data]
pmag = [d[2] for d in data]

def pearson(x, y):
    n = len(x)
    mx, my = sum(x)/n, sum(y)/n
    vx = sum((xi-mx)**2 for xi in x)/n
    vy = sum((yi-my)**2 for yi in y)/n
    cov = sum((xi-mx)*(yi-my) for xi,yi in zip(x,y))/n
    return cov / sqrt(vx*vy) if vx > 0 and vy > 0 else 0

print(f"\nCorr(|sh|, |Re(chi(9))|) = {pearson(sh, rchi):+.4f}")
print(f"Corr(|sh|, |P|)          = {pearson(sh, pmag):+.4f}")
print(f"Corr(|Re(chi(9))|, |P|)  = {pearson(rchi, pmag):+.4f}")
