#!/usr/bin/env python3
"""
Radio amplifier approach: treat C(g) as a signal on (Z/nZ)*
and compute its power spectrum. Factor-aligned periodicity
should appear as spectral peaks.

The autocorrelation R(d) = sum_g C(g) C(gd) is the
collision-collision correlation. Its Fourier transform
|C_hat(chi)|^2 is the power spectrum.

By CRT, characters chi = chi_p x chi_q. The characters
with chi_q = trivial see only the p-component. Their
power |C_hat(chi_p, 1)|^2 should peak at nontrivial chi_p
if p is a factor.

The key question: is the spectral peak detectable from
FEWER than phi(n) values of C(g)?
"""
import cmath, math

b = 10

def collision_count(n, g):
    C = 0
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        if b * r // n == b * (g * r % n) // n:
            C += 1
    return C

def test_radio(p, q):
    n = p * q
    phi_n = (p-1) * (q-1)

    # Compute C(g) for all coprime g
    C = {}
    Q = (n - 1) // b
    for g in range(1, n):
        if math.gcd(g, n) != 1:
            continue
        C[g] = collision_count(n, g) - Q  # deviation

    # Power spectrum via CRT characters
    # chi(g) = exp(2pi i (j_p * log_p(g%p) / (p-1) + j_q * log_q(g%q) / (q-1)))

    # Find generators
    def find_gen(prime):
        for c in range(2, prime):
            v, o = 1, 0
            while True:
                v = v * c % prime
                o += 1
                if v == 1: break
            if o == prime - 1:
                return c
        return None

    gp = find_gen(p)
    gq = find_gen(q)

    dlog_p = {}
    v = 1
    for k in range(p-1):
        dlog_p[v] = k
        v = v * gp % p

    dlog_q = {}
    v = 1
    for k in range(q-1):
        dlog_q[v] = k
        v = v * gq % q

    wp = cmath.exp(2j * cmath.pi / (p-1))
    wq = cmath.exp(2j * cmath.pi / (q-1))

    print(f"n = {p} x {q} = {n}")

    # Compute power spectrum for chi_q = trivial (j_q = 0)
    # These characters see only the p-component
    print(f"\nPower spectrum (chi_q = trivial, sees p-structure):")
    powers_p = []
    for jp in range(p-1):
        # C_hat(jp, 0) = sum_g C(g) * chi_bar(g)
        #              = sum_g C(g) * wp^(-jp * dlog_p[g%p])
        ch = 0
        for g in C:
            gp_res = g % p
            gq_res = g % q
            chi_bar = wp ** (-jp * dlog_p[gp_res])
            ch += C[g] * chi_bar
        ch /= phi_n
        power = abs(ch) ** 2
        powers_p.append(power)

    mean_p = sum(powers_p) / len(powers_p)
    for jp in range(p-1):
        bar = "#" * int(powers_p[jp] / mean_p * 10)
        print(f"  j_p={jp:>3}: |C_hat|^2 = {powers_p[jp]:.6f}  {bar}")

    # Compute power spectrum for chi_p = trivial (j_p = 0)
    # These characters see only the q-component
    print(f"\nPower spectrum (chi_p = trivial, sees q-structure):")
    powers_q = []
    for jq in range(q-1):
        ch = 0
        for g in C:
            gq_res = g % q
            chi_bar = wq ** (-jq * dlog_q[gq_res])
            ch += C[g] * chi_bar
        ch /= phi_n
        power = abs(ch) ** 2
        powers_q.append(power)

    mean_q = sum(powers_q) / len(powers_q)
    for jq in range(q-1):
        bar = "#" * int(powers_q[jq] / mean_q * 10)
        print(f"  j_q={jq:>3}: |C_hat|^2 = {powers_q[jq]:.6f}  {bar}")

    # Compare: "mixed" characters (both nontrivial)
    print(f"\nMixed character power (sample):")
    mixed_total = 0
    mixed_count = 0
    for jp in [1, 2, 3]:
        for jq in [1, 2, 3]:
            ch = 0
            for g in C:
                chi_bar = (wp ** (-jp * dlog_p[g%p])) * (wq ** (-jq * dlog_q[g%q]))
                ch += C[g] * chi_bar
            ch /= phi_n
            power = abs(ch) ** 2
            mixed_total += power
            mixed_count += 1
    print(f"  Mean mixed power: {mixed_total/mixed_count:.6f}")
    print(f"  Mean p-axis power: {mean_p:.6f}")
    print(f"  Mean q-axis power: {mean_q:.6f}")
    print(f"  Ratio p-axis / mixed: {mean_p / (mixed_total/mixed_count):.2f}")
    print(f"  Ratio q-axis / mixed: {mean_q / (mixed_total/mixed_count):.2f}")

test_radio(7, 13)
print("\n" + "="*60 + "\n")
test_radio(13, 17)
print("\n" + "="*60 + "\n")
test_radio(23, 29)
