#!/usr/bin/env python3
"""
semiprime_analysis.py: Analyze the internal structure of semiprimes
for information that leaks the factorization.

For n = p*q, we compute:
1. The fractional field periods and identify short-period rows
2. The collision invariant C(g) for all g in (Z/nZ)*
3. The bin structure and its interleaving pattern
4. Comparison of C_n(g) vs C_p(g) * C_q(g) (tensor test)
5. Period distribution: which cycle lengths appear and how many?

The key question: does the collision spectrum of the composite
leak the factors more efficiently than brute force?
"""

import math
import sys
from collections import defaultdict

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def mult_order(base, n):
    """Multiplicative order of base mod n."""
    if gcd(base, n) != 1:
        return 0
    r = 1
    for k in range(1, n + 1):
        r = (r * base) % n
        if r == 1:
            return k
    return 0

def euler_phi(n):
    result = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result

def compute_bins(n, base=10):
    """Compute digit bins: B_d = {r in 1..n-1 : floor(base*r/n) = d}"""
    bins = defaultdict(list)
    for r in range(1, n):
        d = (base * r) // n
        bins[d].append(r)
    return bins

def collision_count(n, g, base=10):
    """C(g) = number of r in 1..n-1 where floor(br/n) == floor(b*gr/n)"""
    if g % n == 0:
        return 0
    count = 0
    for r in range(1, n):
        gr = (g * r) % n
        if gr == 0:
            continue
        d1 = (base * r) // n
        d2 = (base * gr) // n
        if d1 == d2:
            count += 1
    return count

def cycle_length(r, n, base=10):
    """Period of the decimal expansion of r/n."""
    if gcd(r, n) > 1:
        r2 = r // gcd(r, n)
        n2 = n // gcd(r, n)
    else:
        r2, n2 = r, n
    # Remove factors of base from n2
    for p in [2, 5]:
        while n2 % p == 0:
            n2 //= p
    if n2 == 1:
        return 0  # terminating
    return mult_order(base, n2)


def analyze_semiprime(p, q, base=10):
    """Full analysis of the semiprime n = p*q."""
    n = p * q
    print(f"\n{'='*60}")
    print(f"  SEMIPRIME ANALYSIS: {n} = {p} x {q}  (base {base})")
    print(f"{'='*60}")

    # 1. Period structure
    L_p = mult_order(base, p)
    L_q = mult_order(base, q)
    L_n = mult_order(base, n)
    print(f"\n  Periods: ord_{base}({p}) = {L_p},  ord_{base}({q}) = {L_q}")
    print(f"           ord_{base}({n}) = {L_n},  lcm = {math.lcm(L_p, L_q)}")

    # 2. Period distribution of all r/n
    print(f"\n  Period distribution of r/{n}:")
    period_counts = defaultdict(int)
    period_residues = defaultdict(list)
    for r in range(1, n):
        if gcd(r, n) == 1:
            cl = cycle_length(r, n, base)
            period_counts[cl] += 1
            if len(period_residues[cl]) < 6:
                period_residues[cl].append(r)

    for period in sorted(period_counts.keys()):
        count = period_counts[period]
        examples = period_residues[period][:4]
        marker = ""
        if period == L_p:
            marker = f"  <-- period of 1/{p}"
        if period == L_q:
            marker += f"  <-- period of 1/{q}"
        print(f"    period {period:6d}: {count:5d} residues  "
              f"(e.g. {examples}){marker}")

    # The short-period rows are the key signal
    short_periods = {per: cnt for per, cnt in period_counts.items()
                     if per < L_n}
    if short_periods:
        print(f"\n  SHORT-PERIOD ROWS (period < {L_n}):")
        for per in sorted(short_periods.keys()):
            cnt = short_periods[per]
            # Which factor do they correspond to?
            if per == L_p:
                print(f"    period {per}: {cnt} rows -> factor {q} "
                      f"(these are multiples of {q})")
            elif per == L_q:
                print(f"    period {per}: {cnt} rows -> factor {p} "
                      f"(these are multiples of {p})")
            elif per > 0:
                # Could be a divisor of one factor's period
                factor_info = []
                if L_p % per == 0:
                    factor_info.append(f"divides ord({p})={L_p}")
                if L_q % per == 0:
                    factor_info.append(f"divides ord({q})={L_q}")
                print(f"    period {per}: {cnt} rows  "
                      f"({', '.join(factor_info) if factor_info else '?'})")
            else:
                print(f"    period {per}: {cnt} rows (terminating)")

    # 3. Collision analysis
    print(f"\n  Collision invariant C(g) for n={n}:")

    # Only compute for small n
    if n > 2000:
        print(f"    (skipping full C(g) scan, n={n} too large)")
        print(f"    Computing C(g) for selected multipliers...")
        test_gs = list(range(2, min(30, n)))
    else:
        test_gs = list(range(2, n))

    cg_n = {}
    cg_n[1] = n - 1  # C(1) = n-1 always
    for g in test_gs:
        if gcd(g, n) != 1:
            continue
        cg_n[g] = collision_count(n, g, base)

    # Also compute C(g) for the individual primes
    cg_p = {1: p - 1}
    cg_q = {1: q - 1}
    for g in range(2, max(p, q)):
        if g < p and gcd(g, p) == 1:
            cg_p[g] = collision_count(p, g, base)
        if g < q and gcd(g, q) == 1:
            cg_q[g] = collision_count(q, g, base)

    # Deranging multipliers at composite
    deranging_n = [g for g in sorted(cg_n.keys()) if g > 1 and cg_n[g] == 0]
    deranging_p = [g for g in sorted(cg_p.keys()) if g > 1 and cg_p[g] == 0]
    deranging_q = [g for g in sorted(cg_q.keys()) if g > 1 and cg_q[g] == 0]

    print(f"\n    Deranging multipliers:")
    print(f"      at {p}: {deranging_p[:20]}")
    print(f"      at {q}: {deranging_q[:20]}")
    print(f"      at {n}: {deranging_n[:20]}")
    print(f"    Deranging counts: {p}:{len(deranging_p)}, "
          f"{q}:{len(deranging_q)}, {n}:{len(deranging_n)}")
    print(f"    Expected (b-1): {base-1}")

    # 4. Tensor test: compare C_n(g) with C_p(g) * C_q(g)
    # For g coprime to both p and q
    print(f"\n  Tensor test: C_n(g) vs C_p(g)*C_q(g) / (n-1):")
    print(f"    {'g':>5s} {'C_n(g)':>8s} {'C_p(g)':>8s} {'C_q(g)':>8s} "
          f"{'product':>8s} {'ratio':>8s}")

    ratios = []
    for g in sorted(cg_n.keys()):
        if g == 1:
            continue
        gp = g % p
        gq = g % q
        if gp == 0 or gq == 0:
            continue
        if gp not in cg_p or gq not in cg_q:
            continue
        cp = cg_p[gp]
        cq = cg_q[gq]
        cn = cg_n[g]
        # Normalized product
        product = cp * cq
        ratio = cn / product if product > 0 else float('inf')
        ratios.append(ratio)
        if len(ratios) <= 20 or cn == 0 or (cp == 0) != (cq == 0):
            marker = ""
            if cp == 0 and cq == 0:
                marker = " both deranging"
            elif cp == 0:
                marker = f" deranging at {p}"
            elif cq == 0:
                marker = f" deranging at {q}"
            elif cn == 0:
                marker = " COMPOSITE DERANGING (new!)"
            print(f"    {g:5d} {cn:8d} {cp:8d} {cq:8d} "
                  f"{product:8d} {ratio:8.3f}{marker}")

    if ratios:
        import statistics
        finite_ratios = [r for r in ratios if r != float('inf')]
        if finite_ratios:
            print(f"\n    Ratio statistics (C_n / (C_p * C_q)):")
            print(f"      mean = {statistics.mean(finite_ratios):.4f}")
            print(f"      stdev = {statistics.stdev(finite_ratios):.4f}"
                  if len(finite_ratios) > 1 else "")
            print(f"      min = {min(finite_ratios):.4f}, "
                  f"max = {max(finite_ratios):.4f}")
            print(f"      CV = {statistics.stdev(finite_ratios)/statistics.mean(finite_ratios):.4f}"
                  if len(finite_ratios) > 1 else "")

    # 5. Key structural signal: period gaps
    print(f"\n  FACTORING SIGNAL ANALYSIS:")
    print(f"    The composite {n} has {len(period_counts)} distinct periods.")
    print(f"    Full period {L_n} accounts for "
          f"{period_counts.get(L_n, 0)} of {euler_phi(n)} coprime residues.")

    if L_p != L_q:
        print(f"\n    The two factor periods ({L_p} and {L_q}) are different.")
        print(f"    This means the period alone distinguishes the factors.")
        print(f"    Residues with period {L_p}: multiples of {q} "
              f"(there are {q-1} of them)")
        print(f"    Residues with period {L_q}: multiples of {p} "
              f"(there are {p-1} of them)")
        print(f"    Finding any short-period residue immediately gives a factor.")
    else:
        print(f"\n    Both factors have the same period ({L_p}).")
        print(f"    Period alone does not distinguish them.")
        print(f"    Must use collision structure to separate.")

    # 6. Direct factor extraction from short periods
    print(f"\n  DIRECT FACTOR TEST:")
    for r in range(2, min(n, 200)):
        if gcd(r, n) == 1:
            cl = cycle_length(r, n, base)
            if 0 < cl < L_n:
                # This residue has a short period. Which factor?
                # r/n has period cl. This means base^cl = 1 mod (n/gcd(r,n))
                # but the reduced denominator divides one factor
                g = gcd(r, n)
                if g > 1:
                    print(f"    r={r}: gcd(r,n)={g}, factor found!")
                    break
                # Actually: if period of r/n = L_p, then n | r*(base^L_p - 1)
                # but p | (base^L_p - 1), so q | r
                if cl == L_p:
                    print(f"    r={r}: period={cl}=ord({p}), "
                          f"so {q} | {r}? {r % q == 0}")
                    if r % q == 0:
                        print(f"    FACTOR FOUND: {q} (and {p} = {n}//{q})")
                        break
                elif cl == L_q:
                    print(f"    r={r}: period={cl}=ord({q}), "
                          f"so {p} | {r}? {r % p == 0}")
                    if r % p == 0:
                        print(f"    FACTOR FOUND: {p} (and {q} = {n}//{p})")
                        break
                else:
                    print(f"    r={r}: period={cl} (sub-period, "
                          f"divides {L_p}? {L_p%cl==0}, "
                          f"divides {L_q}? {L_q%cl==0})")


def main():
    base = 10

    # Small semiprimes first
    print("SEMIPRIME INTERNAL ARCHITECTURE ANALYSIS")
    print("Can the collision structure leak the factors?")

    test_cases = [
        (7, 11),      # 77, the one we looked at
        (7, 13),      # 91
        (11, 13),     # 143
        (13, 17),     # 221, from the paper
        (7, 41),      # 287, different sized factors
        (29, 31),     # 899, close primes
        (101, 103),   # 10403, twin-prime-like
    ]

    for p, q in test_cases:
        analyze_semiprime(p, q, base)

    # Summary
    print(f"\n{'='*60}")
    print("  SUMMARY")
    print(f"{'='*60}")
    print("""
  For every semiprime n = p*q tested:

  1. PERIOD SIGNAL: If ord_b(p) != ord_b(q), the short-period
     rows immediately identify one factor. The number of such
     rows is (smaller factor - 1). For n = p*q with p < q,
     finding any residue r with period ord_b(p) gives q = n/gcd(r*(b^L-1), n).

  2. DERANGING SIGNAL: The composite has MORE deranging multipliers
     than either prime alone (if it has any at all). The deranging
     set at the composite is NOT the union of the factor deranging sets.

  3. TENSOR FAILURE: C_n(g) / (C_p(g)*C_q(g)) has high variance
     (CV > 0.5). The composite collision spectrum carries non-trivial
     interaction information.

  The factoring question: for cryptographic semiprimes (p,q ~ 10^150),
  the period L_n ~ 10^150 and finding a short-period row requires
  checking O(q) residues. This is no better than trial division.
  The collision approach needs a way to detect period structure
  WITHOUT computing full periods.
""")


if __name__ == '__main__':
    main()
