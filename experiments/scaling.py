#!/usr/bin/env python3
"""
How does the ghost correlation signal scale with factor size?

For composites n = pq with increasing p and q, compute
the correlation excess at d ≡ 1 mod p and mod q.

If excess ~ 1/p: need O(p²) samples to detect. Wall holds.
If excess ~ 1/sqrt(p): need O(p) samples. Tunnel opens.
If excess ~ constant: need O(1) samples. Wall falls.
"""
import math

b = 10

def correlation_excess(n, m):
    """Compute correlation excess at d ≡ 1 mod m, excluding d < m."""
    both_1 = 0
    one_1 = 0
    both_other = 0
    one_other = 0

    # Sample distances to keep runtime manageable
    for d in range(2, n):
        if math.gcd(d, n) != 1:
            continue

        both = 0
        one = 0

        # Sample r and g
        for r in range(1, n):
            if math.gcd(r, n) != 1:
                continue
            for g in range(2, min(n, 40)):
                if math.gcd(g, n) != 1:
                    continue
                gd = g * d % n
                if math.gcd(gd, n) != 1:
                    continue

                d1 = b * r // n
                gr1 = g * r % n
                x1 = (d1 == b * gr1 // n)

                gr2 = gd * r % n
                x2 = (d1 == b * gr2 // n)

                if x1:
                    one += 1
                    if x2:
                        both += 1

        k = d % m
        if k == 1:
            both_1 += both
            one_1 += one
        elif k != 0:
            both_other += both
            one_other += one

    corr_1 = both_1 / one_1 if one_1 > 0 else 0
    corr_other = both_other / one_other if one_other > 0 else 0
    excess = corr_1 - corr_other

    return corr_1, corr_other, excess

composites = [
    (7, 13, 91),
    (7, 17, 119),
    (7, 23, 161),
    (13, 17, 221),
    (13, 23, 299),
    (17, 23, 391),
    (23, 29, 667),
]

print(f"{'n':>6} {'p':>3} {'q':>3} | "
      f"{'corr1_p':>8} {'bg_p':>8} {'exc_p':>8} | "
      f"{'corr1_q':>8} {'bg_q':>8} {'exc_q':>8}")
print("-" * 80)

for p, q, n in composites:
    c1_p, bg_p, exc_p = correlation_excess(n, p)
    c1_q, bg_q, exc_q = correlation_excess(n, q)
    print(f"{n:6d} {p:3d} {q:3d} | "
          f"{c1_p:8.5f} {bg_p:8.5f} {exc_p:+8.5f} | "
          f"{c1_q:8.5f} {bg_q:8.5f} {exc_q:+8.5f}")
