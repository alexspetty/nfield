#!/usr/bin/env python3
"""
Compute the collision transform coefficients s_hat(chi) for odd characters
mod m = b^2, and examine the sign structure of s_hat(chi) * P(s, chi).

For each odd character chi mod m:
  s_hat(chi) = (1/phi(m)) * sum_a S°(a) * chi_bar(a)
  P(s, chi) = sum_p chi(p) / p^s  (partial sum)

We want to check: does Re(s_hat(chi) * P(s, chi)) >= 0 for all odd chi?
"""

from math import gcd, log, sqrt, pi, cos, sin, atan2
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

def primitive_root(n):
    """Find a primitive root mod n (works for prime powers, 2*prime powers)."""
    phi = n
    temp = n
    primes = []
    for p in range(2, int(sqrt(n)) + 2):
        if temp % p == 0:
            primes.append(p)
            phi = phi // p * (p - 1)
            while temp % p == 0:
                temp //= p
    if temp > 1:
        primes.append(temp)
        phi = phi // temp * (temp - 1)

    for g in range(2, n):
        if gcd(g, n) != 1:
            continue
        ok = True
        for p in primes:
            if pow(g, phi // p, n) == 1:
                ok = False
                break
        if ok:
            return g, phi
    return None, phi

def get_characters(m):
    """
    Get all Dirichlet characters mod m using discrete log.
    Returns list of (chi_values, is_odd) where chi_values[a] = chi(a).
    """
    units = [a for a in range(1, m) if gcd(a, m) == 1]
    phi_m = len(units)

    # For m = b^2, we need the group structure
    # Use brute force: enumerate all characters via discrete log
    # if m has a primitive root

    g, phi = primitive_root(m)
    if g is None:
        # No primitive root; m is not prime power or 2*prime power
        # Use a different approach for composite m
        return None

    # discrete log table
    dlog = {}
    val = 1
    for k in range(phi):
        dlog[val] = k
        val = val * g % m

    # Characters: chi_j(g^k) = exp(2*pi*i*j*k/phi)
    characters = []
    for j in range(phi):
        chi = {}
        for a in range(m):
            if gcd(a, m) != 1:
                chi[a] = 0
            else:
                k = dlog[a]
                angle = 2 * pi * j * k / phi
                chi[a] = complex(cos(angle), sin(angle))

        # Check if odd: chi(-1) = -1
        minus1 = m - 1  # -1 mod m
        is_odd = abs(chi[minus1] - (-1)) < 1e-6
        is_trivial = (j == 0)

        characters.append({
            'index': j,
            'values': chi,
            'is_odd': is_odd,
            'is_trivial': is_trivial
        })

    return characters

def main():
    b = 10
    m = b * b

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
            R = (a - 1) % b
            cls[R].append(S_table[a])
    mean_R = {R: sum(v)/len(v) for R, v in cls.items()}

    S_cent = {}
    for a in units:
        if a in S_table:
            S_cent[a] = S_table[a] - mean_R[(a - 1) % b]

    print(f"Base {b}, m = {m}, phi(m) = {phi_m}")
    print(f"Units with S° computed: {len(S_cent)}")
    print()

    # Get characters
    chars = get_characters(m)
    if chars is None:
        print("No primitive root; need different approach")
        return

    # Compute s_hat(chi) for each odd character
    odd_chars = [c for c in chars if c['is_odd']]
    print(f"Total characters: {len(chars)}")
    print(f"Odd characters: {len(odd_chars)}")
    print()

    # Compute transform coefficients
    for c in odd_chars:
        chi = c['values']
        s_hat = 0
        for a in units:
            if a in S_cent:
                s_hat += S_cent[a] * chi[a].conjugate()
        s_hat /= phi_m
        c['s_hat'] = s_hat

    # Compute P(s, chi) = sum_p chi(p)/p^s for several s values
    s_values = [1.0, 0.9, 0.8, 0.7, 0.6, 0.5]

    # Accumulate prime character sums
    for c in odd_chars:
        c['P'] = {s: 0.0 for s in s_values}

    count = 0
    for p in range(m + 1, 2000000):
        if not is_prime(p) or gcd(p, b) != 1:
            continue
        count += 1
        for c in odd_chars:
            chi_p = c['values'][p % m]
            for s in s_values:
                c['P'][s] += chi_p * p ** (-s)

    print(f"Primes used for P(s, chi): {count}")
    print()

    # Now check the sign of Re(s_hat * P(s, chi))
    for s in s_values:
        print(f"=== s = {s} ===")
        print(f"{'j':>4} {'|s_hat|':>8} {'arg(s_hat)':>10} "
              f"{'|P|':>8} {'arg(P)':>8} "
              f"{'Re(s_hat*P)':>12} {'sign':>5}")

        all_positive = True
        for c in odd_chars:
            sh = c['s_hat']
            P = c['P'][s]
            product = sh * P

            re_prod = product.real
            sign = '+' if re_prod >= 0 else '-'
            if re_prod < -1e-10:
                all_positive = False

            print(f"{c['index']:>4} {abs(sh):>8.4f} {atan2(sh.imag, sh.real):>+10.4f} "
                  f"{abs(P):>8.4f} {atan2(P.imag, P.real):>+8.4f} "
                  f"{re_prod:>+12.6f} {sign:>5}")

        print(f"All Re(s_hat * P) >= 0: {all_positive}")
        print()

if __name__ == '__main__':
    main()
