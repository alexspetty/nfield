#!/usr/bin/env python3
"""Verify checkerboard at multiple composites."""
import cmath, math

def test_composite(p, q, g_p, g_q):
    n = p * q

    def make_dlog(prime, gen):
        dlog = {}
        v = 1
        for k in range(prime - 1):
            dlog[v] = k
            v = v * gen % prime
        return dlog

    dl_p = make_dlog(p, g_p)
    dl_q = make_dlog(q, g_q)
    w_p = cmath.exp(2j * cmath.pi / (p-1))
    w_q = cmath.exp(2j * cmath.pi / (q-1))

    # chi(-1) for each character index
    # chi_p(-1) = w_p^(jp * dl_p[p-1])
    dl_m1_p = dl_p[p-1]
    dl_m1_q = dl_q[q-1]

    zero_count = 0
    nonzero_count = 0
    violations = 0

    for jp in range(p-1):
        for jq in range(q-1):
            # Compute B_1
            s = 0
            for a in range(1, n):
                if math.gcd(a, n) != 1:
                    continue
                ap, aq = a % p, a % q
                chi_bar = (w_p ** (-jp * dl_p[ap])) * (w_q ** (-jq * dl_q[aq]))
                s += a * chi_bar
            B1 = abs(s / n)

            # Parity of composite character
            chi_p_m1 = w_p ** (jp * dl_m1_p)
            chi_q_m1 = w_q ** (jq * dl_m1_q)
            composite_even = abs(chi_p_m1.real * chi_q_m1.real - 1) < 0.01  # both same sign

            # Actually: chi(-1) = chi_p(-1) * chi_q(-1)
            chi_m1 = chi_p_m1 * chi_q_m1
            is_even = abs(chi_m1.real - 1) < 0.01

            if is_even:
                if B1 > 1e-6:
                    violations += 1
                else:
                    zero_count += 1
            else:
                nonzero_count += 1

    print(f"n = {p} x {q} = {n}: "
          f"even chars with B1=0: {zero_count}, "
          f"odd chars (B1 generally nonzero): {nonzero_count}, "
          f"violations: {violations}")

test_composite(7, 11, 3, 2)
test_composite(5, 7, 2, 3)
test_composite(13, 17, 2, 3)
test_composite(7, 13, 3, 2)
test_composite(11, 13, 2, 2)
