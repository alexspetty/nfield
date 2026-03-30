#!/usr/bin/env python3
"""Verify Parseval identity with decomposition theorem."""
import cmath, math
from collections import defaultdict

def run(b):
    m = b * b
    units = [a for a in range(1, m) if math.gcd(a, m) == 1]
    phi = len(units)

    # Generator
    g = None
    for c in range(2, m):
        if math.gcd(c, m) != 1: continue
        v, o = 1, 0
        while True:
            v = v * c % m; o += 1
            if v == 1: break
        if o == phi: g = c; break

    dlog = {}; v = 1
    for k in range(phi):
        dlog[v] = k; v = v * g % m

    # Build S, center
    S = {}
    for p in range(m+1, 50000):
        if p < 2: continue
        if any(p % i == 0 for i in range(2, int(p**0.5)+1)): continue
        if math.gcd(p, b) != 1: continue
        a = p % m
        if a in S: continue
        C = sum(1 for r in range(1, p) if b*r//p == b*(b*r%p)//p)
        S[a] = C - (p-1)//b

    cls = defaultdict(list)
    for a in units:
        if a in S: cls[(a-1)%b].append(S[a])
    mean_R = {R: sum(v)/len(v) for R, v in cls.items()}
    Sc = {a: S[a] - mean_R[(a-1)%b] for a in units if a in S}

    # RHS of Parseval: (1/phi) sum |S°(a)|^2
    rhs = sum(Sc[a]**2 for a in units if a in Sc) / phi

    # LHS: sum |s_hat(chi)|^2 over odd characters
    w = cmath.exp(2j * cmath.pi / phi)
    dl_m1 = dlog[m-1]

    lhs = 0
    lhs_prim = 0
    lhs_imprim = 0

    for j in range(phi):
        if (2 * j * dl_m1) % (2 * phi) != phi: continue  # odd only

        sh = sum(Sc.get(a, 0) * w**(-j*dlog[a]) for a in units) / phi
        sh_mag2 = abs(sh)**2
        lhs += sh_mag2

        # Check if primitive: is the partial sum zero?
        ps = sum(w**(-j*dlog[k]) for k in range(1, b) if k in dlog)
        if abs(ps) < 1e-6:
            lhs_imprim += sh_mag2
        else:
            lhs_prim += sh_mag2

    # Decomposition: sum |B1|^2 |S_G|^2 / phi^2
    decomp = 0
    for j in range(phi):
        if (2 * j * dl_m1) % (2 * phi) != phi: continue
        ps = sum(w**(-j*dlog[k]) for k in range(1, b) if k in dlog)
        if abs(ps) < 1e-6: continue  # skip imprimitive

        B1 = sum(a * w**(-j*dlog[a]) for a in units) / m

        # S_G via factorization
        bp1 = (b+1) % m
        if bp1 in dlog:
            cb = w**(-j*dlog[bp1])
        else:
            cb = 0
        SG = -2 * cb * ps

        decomp += (abs(B1)**2 * abs(SG)**2) / phi**2

    print(f"Base {b}: Parseval RHS = {rhs:.6f}")
    print(f"  LHS (all odd)  = {lhs:.6f}  match={abs(lhs-rhs)<1e-4}")
    print(f"  LHS (primitive)= {lhs_prim:.6f}")
    print(f"  LHS (imprimitive)= {lhs_imprim:.6f}")
    print(f"  Decomp sum     = {decomp:.6f}  match_prim={abs(decomp-lhs_prim)<1e-4}")

    # The L-value moment: sum |L(1)|^2 |S_G|^2
    # = phi^2 * decomp = phi^2 * rhs (if imprimitive contribute 0)
    # = phi * sum |S°(a)|^2
    moment = phi * rhs * (math.pi / b)**2
    print(f"  => sum |L(1)|^2 |S_G|^2 / phi = {moment:.6f}")
    print(f"     (pi/b)^2 * sum |S°|^2 = {(math.pi/b)**2 * sum(Sc[a]**2 for a in units if a in Sc):.6f}")
    print()

for b in [5, 7, 11, 13]:
    run(b)
