#!/usr/bin/env python3
"""Verify: B_1(chi_p x chi_q) = 0 for both non-trivial."""
import cmath, math

p, q = 7, 11
n = p * q

def make_dlog(prime, gen):
    dlog = {}
    v = 1
    for k in range(prime - 1):
        dlog[v] = k
        v = v * gen % prime
    return dlog

dl_p = make_dlog(7, 3)
dl_q = make_dlog(11, 2)
w_p = cmath.exp(2j * cmath.pi / 6)
w_q = cmath.exp(2j * cmath.pi / 10)

print(f"B_1(chi_p[jp] x chi_q[jq]) for n = {p} x {q}:")
print(f"{'jp':>3} {'jq':>3} {'|B1|':>12} {'p_triv':>7} {'q_triv':>7}")

for jp in range(p-1):
    for jq in range(q-1):
        s = 0
        for a in range(1, n):
            if math.gcd(a, n) != 1:
                continue
            ap, aq = a % p, a % q
            chi_bar = (w_p ** (-jp * dl_p[ap])) * (w_q ** (-jq * dl_q[aq]))
            s += a * chi_bar
        B1 = s / n
        pt = "yes" if jp == 0 else "no"
        qt = "yes" if jq == 0 else "no"
        print(f"{jp:3d} {jq:3d} {abs(B1):12.8f} {pt:>7} {qt:>7}")
