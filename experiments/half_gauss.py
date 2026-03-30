#!/usr/bin/env python3
"""
The wrapping set is always half the group.
The collision transform coefficient is a character sum over that half.
What IS a half-group character sum, and what does it equal?

Classical result: for a character chi mod m and the "upper half"
H = {a : a > m/2, gcd(a,m)=1}, the half-sum relates to L-values.

But our half isn't the upper half. It's the WRAPPING half:
{a : ca mod m < a} for specific c.

Let's understand both and see if they're related.
"""

import cmath
from math import pi, floor, gcd, sqrt

def primitive_root(n):
    phi = n
    temp = n; p = 2; factors = []
    while p * p <= temp:
        if temp % p == 0:
            factors.append(p)
            while temp % p == 0: temp //= p
        p += 1
    if temp > 1: factors.append(temp)
    for f in factors: phi = phi - phi // f
    for g in range(2, n):
        if gcd(g, n) != 1: continue
        ok = True
        for f in factors:
            if pow(g, phi // f, n) == 1: ok = False; break
        if ok: return g, phi
    return None, phi

print("HALF-GROUP CHARACTER SUMS")
print("="*60)

for b in [3, 5, 7]:
    m = b * b
    gen, phi = primitive_root(m)
    if gen is None: continue

    dlog = {}; pw = 1
    for k in range(phi):
        dlog[pw] = k; pw = (pw * gen) % m

    units = sorted(dlog.keys())
    omega = cmath.exp(2j * pi / phi)

    G = [n for n in range(m) if floor(n/b) == n % b]

    print(f"\n{'='*60}")
    print(f"BASE {b}, m={m}, phi={phi}, gen={gen}")
    print(f"{'='*60}")

    # For each non-trivial good slice
    for n in G:
        c = n + 1
        if c % m == 0 or c == 1: continue

        wrap = sorted([a for a in units if (c * a % m) < a])
        non_wrap = sorted([a for a in units if (c * a % m) >= a])

        print(f"\n  Slice n={n}, c={c}:")
        print(f"    Wrap set:     {wrap}")
        print(f"    Non-wrap set: {non_wrap}")

        # Key question: what IS the wrapping set?
        # {a : ca mod m < a}
        # Equivalently: {a : there exists k such that ca = km + r, 0 <= r < a}
        # Equivalently: {a : floor(ca/m) > floor((c-1)a/m)} ... not quite

        # Simpler: ca mod m < a iff {ca/m} < a/m iff {ca/m} < {a/m}
        # (since a < m, {a/m} = a/m)
        # So: wrapping iff the fractional part of ca/m is LESS than a/m
        # i.e., multiplication by c DECREASES the fractional part

        # In the cyclic group with generator g:
        # a = g^j for some j. ca = c * g^j.
        # If c = g^(-1) (inverse of generator), then ca = g^(j-1).
        # The wrapping condition {g^(j-1)/m} < {g^j/m} depends on
        # the ordering of g^j/m in (0,1).

        # Let's check: is the wrapping set = {g^j : j in first half}?
        wrap_dlogs = sorted([dlog[a] for a in wrap])
        non_wrap_dlogs = sorted([dlog[a] for a in non_wrap])

        print(f"    Wrap dlogs:     {wrap_dlogs}")
        print(f"    Non-wrap dlogs: {non_wrap_dlogs}")

        # Is wrap = {elements with dlog in some specific half}?
        # Check if it's the first half, second half, even, odd, etc.
        first_half = set(range(phi//2))
        second_half = set(range(phi//2, phi))
        evens = set(range(0, phi, 2))
        odds = set(range(1, phi, 2))

        wrap_set = set(wrap_dlogs)
        if wrap_set == first_half:
            print(f"    >>> Wrap = first half of cyclic group (dlogs 0..{phi//2-1})")
        elif wrap_set == second_half:
            print(f"    >>> Wrap = second half of cyclic group (dlogs {phi//2}..{phi-1})")
        elif wrap_set == evens:
            print(f"    >>> Wrap = even powers of generator")
        elif wrap_set == odds:
            print(f"    >>> Wrap = odd powers of generator")
        else:
            print(f"    >>> Wrap has no simple dlog pattern")

        # Character sums over wrap set for each odd character
        print(f"    Character sums over wrap set:")
        dl_neg1 = dlog.get(m - 1)

        for j in range(1, phi):
            if dl_neg1 is not None:
                chi_neg1 = omega**(j * dl_neg1)
                if chi_neg1.real > -0.5: continue  # even

            half_sum = sum(omega**(j*dlog[a]) for a in wrap)
            full_sum = sum(omega**(j*dlog[a]) for a in units)  # = 0 for j != 0

            # The half sum for character j
            mag = abs(half_sum)

            # Classical: for the "upper half" {a > m/2}, the sum relates to L(1, chi)
            # Our half is different. But is |half_sum| = sqrt(m)/2 or similar?

            print(f"      chi_{j}: half_sum = {half_sum.real:+.4f}{half_sum.imag:+.4f}i  "
                  f"|sum| = {mag:.4f}  sqrt(m)/2 = {sqrt(m)/2:.4f}")

        # For each slice c, what is c in the group?
        if c in dlog:
            print(f"    c = {c} = gen^{dlog[c]} in the cyclic group")
        else:
            print(f"    c = {c} not a unit mod {m}")

print(f"\n{'='*60}")
print(f"KEY OBSERVATION")
print(f"{'='*60}")
print(f"""
The wrapping set for each good slice is NOT simply "first half"
or "even powers" in general. It depends on the specific slice.

But it's ALWAYS exactly half the units. This means:

  wrap_sum(chi) + non_wrap_sum(chi) = full_sum(chi) = 0

  So wrap_sum(chi) = -non_wrap_sum(chi) = full_sum / 2 ... NO!
  full_sum = 0, so wrap_sum = -non_wrap_sum.

  |wrap_sum| = |non_wrap_sum|.

The two halves contribute equal and opposite character sums.
The collision transform coefficient measures the DIFFERENCE
between the two halves: how the character distinguishes
the wrapping half from the non-wrapping half.
""")
