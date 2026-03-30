#!/usr/bin/env python3
"""
Detailed sign structure: which characters are positive, which negative?
Look for patterns in the character indices, orders, and conductors.
"""

from math import gcd, pi, cos, sin, atan2
from collections import defaultdict

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def build_chars_mod100():
    """
    (Z/100Z)* = (Z/4Z)* x (Z/25Z)*
    Z/4Z* = {1,3}, gen by 3, order 2
    Z/25Z* is cyclic of order 20, gen by 2

    Character chi_{j,k}(a) = chi4_j(a mod 4) * chi25_k(a mod 25)
    where j in {0,1}, k in {0,...,19}
    """
    # Discrete log mod 25, generator 2
    g25 = 2
    dlog25 = {}
    val = 1
    for i in range(20):
        dlog25[val] = i
        val = val * g25 % 25

    # Discrete log mod 4, generator 3
    dlog4 = {1: 0, 3: 1}

    chars = []
    for j in range(2):       # index into Z/4Z*
        for k in range(20):  # index into Z/25Z*
            chi = {}
            for a in range(100):
                if gcd(a, 100) != 1:
                    chi[a] = 0
                else:
                    a4 = a % 4
                    a25 = a % 25
                    angle4 = pi * j * dlog4[a4]  # 2*pi*j*dlog/2
                    angle25 = 2 * pi * k * dlog25[a25] / 20
                    chi[a] = complex(cos(angle4 + angle25),
                                     sin(angle4 + angle25))

            # chi(-1) = chi(99)
            val_minus1 = chi[99]
            is_odd = abs(val_minus1 - (-1)) < 1e-6
            is_even = abs(val_minus1 - 1) < 1e-6

            # Order of the character
            order = 1
            if j == 0 and k == 0:
                order = 1
            else:
                for o in range(1, 41):
                    # chi^o should be trivial
                    all_one = True
                    for a in [3, 7, 11, 13]:
                        v = chi[a] ** o
                        if abs(v - 1) > 1e-6:
                            all_one = False
                            break
                    if all_one:
                        order = o
                        break

            # Is it real?
            is_real = all(abs(chi[a].imag) < 1e-6
                        for a in range(100) if gcd(a, 100) == 1)

            # Conductor (smallest modulus that induces this character)
            # For characters of (Z/4Z)* x (Z/25Z)*:
            # conductor = lcm(cond4, cond25)
            if j == 0:
                cond4 = 1
            else:
                cond4 = 4

            if k == 0:
                cond25 = 1
            elif k % 5 == 0:
                cond25 = 5
            else:
                cond25 = 25

            from math import lcm
            conductor = lcm(cond4, cond25)

            chars.append({
                'j': j, 'k': k,
                'chi': chi,
                'is_odd': is_odd,
                'is_even': is_even,
                'order': order,
                'is_real': is_real,
                'conductor': conductor
            })

    return chars

def main():
    b = 10
    m = 100

    # Build S table
    S_table = {}
    for p in range(m + 1, 50000):
        if not is_prime(p) or gcd(p, b) != 1:
            continue
        a = p % m
        if a in S_table:
            continue
        C = sum(1 for r in range(1, p)
                if b * r // p == b * (b * r % p) // p)
        S_table[a] = C - (p - 1) // b

    units = [a for a in range(1, m) if gcd(a, m) == 1]
    phi_m = len(units)

    # Class means for centering
    cls = defaultdict(list)
    for a in units:
        if a in S_table:
            cls[(a - 1) % b].append(S_table[a])
    mean_R = {R: sum(v)/len(v) for R, v in cls.items()}

    S_cent = {}
    for a in units:
        if a in S_table:
            S_cent[a] = S_table[a] - mean_R[(a - 1) % b]

    # Build characters
    chars = build_chars_mod100()

    # Compute s_hat for each
    for c in chars:
        chi = c['chi']
        s_hat = sum(S_cent.get(a, 0) * chi.get(a, 0).conjugate()
                    for a in units) / phi_m
        c['s_hat'] = complex(s_hat)

    odd_chars = [c for c in chars if c['is_odd']]

    # Compute P(s, chi) at s = 0.5
    for c in odd_chars:
        c['P05'] = complex(0)

    count = 0
    for p in range(m + 1, 5000000):
        if not is_prime(p) or gcd(p, b) != 1:
            continue
        count += 1
        a = p % m
        for c in odd_chars:
            chi_p = c['chi'].get(a, 0)
            if chi_p == 0: continue
            c['P05'] += chi_p * p ** (-0.5)

    print(f"Base {b}, m={m}, {count} primes")
    print(f"Odd characters: {len(odd_chars)}")
    print()

    print(f"{'j':>2} {'k':>3} {'ord':>4} {'real':>5} {'cond':>5} "
          f"{'|s_hat|':>8} {'arg(sh)/pi':>10} "
          f"{'Re(sh*P)':>10} {'sign':>5} {'a mod 3':>8}")

    for c in sorted(odd_chars, key=lambda x: (x['j'], x['k'])):
        sh = c['s_hat']
        P = c['P05']
        prod = sh * P
        sign = '+' if prod.real >= -1e-10 else '-'

        # What mod-3 class does this character "see"?
        # chi restricted to mod 3
        v1 = c['chi'][1]   # a = 1 mod 3 (pick a=1)
        v2 = c['chi'][2]   # a = 2 mod 3 (pick a=2)
        # Actually need units... let me check chi(7) vs chi(11)
        # 7 mod 3 = 1, 11 mod 3 = 2
        chi7 = c['chi'][7]
        chi11 = c['chi'][11]
        # If chi is trivial on mod-3 classes: chi7/chi7 ~ chi11/chi11

        print(f"{c['j']:>2} {c['k']:>3} {c['order']:>4} "
              f"{'Y' if c['is_real'] else 'N':>5} {c['conductor']:>5} "
              f"{abs(sh):>8.4f} {atan2(sh.imag, sh.real)/pi:>+10.4f} "
              f"{prod.real:>+10.4f} {sign:>5}")

    print()

    # Check: do the negative ones share a property?
    neg = [c for c in odd_chars if (c['s_hat'] * c['P05']).real < -1e-10]
    pos = [c for c in odd_chars if (c['s_hat'] * c['P05']).real >= -1e-10]

    print("NEGATIVE characters:")
    for c in neg:
        print(f"  j={c['j']} k={c['k']} order={c['order']} "
              f"conductor={c['conductor']} real={c['is_real']}")

    print("\nPOSITIVE characters:")
    for c in pos:
        print(f"  j={c['j']} k={c['k']} order={c['order']} "
              f"conductor={c['conductor']} real={c['is_real']}")

    # Check: is there a pattern by conductor?
    print("\nBy conductor:")
    for cond in sorted(set(c['conductor'] for c in odd_chars)):
        subset = [c for c in odd_chars if c['conductor'] == cond]
        n_neg = sum(1 for c in subset
                    if (c['s_hat'] * c['P05']).real < -1e-10)
        n_pos = len(subset) - n_neg
        print(f"  conductor {cond}: {n_pos} positive, {n_neg} negative")

    # Check: by order
    print("\nBy order:")
    for order in sorted(set(c['order'] for c in odd_chars)):
        subset = [c for c in odd_chars if c['order'] == order]
        n_neg = sum(1 for c in subset
                    if (c['s_hat'] * c['P05']).real < -1e-10)
        n_pos = len(subset) - n_neg
        print(f"  order {order}: {n_pos} positive, {n_neg} negative")

    # Check: do conjugate pairs have opposite signs?
    print("\nConjugate pair check (j, k) vs (j, 20-k):")
    seen = set()
    for c in odd_chars:
        j, k = c['j'], c['k']
        if (j, k) in seen:
            continue
        # conjugate is (j, (20-k) % 20) for the Z/25Z part
        k_conj = (20 - k) % 20
        partner = None
        for c2 in odd_chars:
            if c2['j'] == j and c2['k'] == k_conj:
                partner = c2
                break
        if partner and (j, k_conj) != (j, k):
            s1 = '+' if (c['s_hat'] * c['P05']).real >= -1e-10 else '-'
            s2 = '+' if (partner['s_hat'] * partner['P05']).real >= -1e-10 else '-'
            print(f"  ({j},{k:>2}) {s1}  <->  ({j},{k_conj:>2}) {s2}  "
                  f"{'SAME' if s1 == s2 else 'DIFF'}")
            seen.add((j, k))
            seen.add((j, k_conj))
        elif (j, k_conj) == (j, k):
            s1 = '+' if (c['s_hat'] * c['P05']).real >= -1e-10 else '-'
            print(f"  ({j},{k:>2}) {s1}  (self-conjugate)")
            seen.add((j, k))

if __name__ == '__main__':
    main()
