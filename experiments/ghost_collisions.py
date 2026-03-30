#!/usr/bin/env python3
"""
Count ghost collisions across multiple composites and multipliers.
Ghost collision: composite collides but neither prime does individually.
"""
import math

def modinv(a, m):
    g, x = 0, 1
    a0, m0 = a % m, m
    while a0 != 0:
        q = m0 // a0
        m0, a0 = a0, m0 - q * a0
        g, x = x, g - q * x
    return g % m

b = 10

def analyze(p, q):
    n = p * q
    qi = modinv(q, p)
    pi = modinv(p, q)

    def crt(rp, rq):
        return (rp * q * qi + rq * p * pi) % n

    # For each multiplier g, count ghost collisions
    total_ghost = 0
    total_composite = 0
    total_tensor = 0
    n_mults = 0

    for g in range(2, n):
        if math.gcd(g, n) != 1:
            continue
        n_mults += 1

        ghost = 0
        comp = 0
        tens = 0

        for rp in range(1, p):
            for rq in range(1, q):
                r = crt(rp, rq)
                if math.gcd(r, n) != 1:
                    continue

                gr = g * r % n
                grp, grq = gr % p, gr % q

                dp = b * rp // p
                dq = b * rq // q
                dp2 = b * grp // p
                dq2 = b * grq // q

                d_n = b * r // n
                d_n2 = b * gr // n

                coll_p = (dp == dp2)
                coll_q = (dq == dq2)
                coll_n = (d_n == d_n2)

                if coll_n:
                    comp += 1
                if coll_p and coll_q:
                    tens += 1
                if coll_n and not (coll_p and coll_q):
                    ghost += 1

        total_ghost += ghost
        total_composite += comp
        total_tensor += tens

    mean_ghost = total_ghost / n_mults
    mean_comp = total_composite / n_mults
    mean_tens = total_tensor / n_mults

    print(f"n = {p} x {q} = {n:>5}: "
          f"mean C(composite) = {mean_comp:6.2f}, "
          f"mean C(tensor) = {mean_tens:6.2f}, "
          f"mean ghost = {mean_ghost:6.2f}, "
          f"ghost/composite = {mean_ghost/mean_comp:.3f}" if mean_comp > 0 else "")

# Test across several composites
for p, q in [(7, 11), (7, 13), (11, 13), (7, 17), (13, 17),
             (7, 19), (11, 17), (7, 23), (11, 19)]:
    analyze(p, q)
