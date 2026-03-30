#!/usr/bin/env python3
"""
Look for a formula for R(g) in terms of the pairwise distances.
R(g) = sum_r N(r, gr mod p) where N counts same-bin bases.
"""

def N_exact(r, s, p):
    """Exact count of bases b in {2,...,p-1} where floor(br/p) = floor(bs/p)."""
    if r == s:
        return p - 2  # all bases
    count = 0
    for b in range(2, p):
        if b * r // p == b * s // p:
            count += 1
    return count

def analyze_prime(p):
    print(f"\np = {p}")

    # For g = p-1 (order 2, reflection): R(g) should be minimal
    g = p - 1
    R_reflect = 0
    for r in range(1, p):
        s = (g * r) % p  # s = p - r
        R_reflect += N_exact(r, s, p)
    print(f"  g = p-1 = {g}: R = {R_reflect}")

    # For g = 2:
    g = 2
    # Compute R and also the "distance spectrum"
    dist_counts = {}
    R_2 = 0
    for r in range(1, p):
        s = (g * r) % p
        d = min(abs(r - s), p - abs(r - s))
        N = N_exact(r, s, p)
        R_2 += N
        if d not in dist_counts:
            dist_counts[d] = {'count': 0, 'N_sum': 0}
        dist_counts[d]['count'] += 1
        dist_counts[d]['N_sum'] += N

    print(f"  g = 2: R = {R_2}")
    print(f"  Distance spectrum for g=2:")
    print(f"    {'d':>4} {'#pairs':>7} {'N_sum':>7} {'N_avg':>7}")
    for d in sorted(dist_counts.keys()):
        dc = dist_counts[d]
        print(f"    {d:>4} {dc['count']:>7} {dc['N_sum']:>7} {dc['N_sum']/dc['count']:>7.1f}")

    # Key test: is N(r, s) a function of min(|r-s|, p-|r-s|) alone?
    print(f"\n  Is N(r,s) a function of distance alone?")
    for d in sorted(dist_counts.keys())[:5]:
        # Check if all pairs at distance d have the same N
        N_values = set()
        for r in range(1, p):
            s = (2 * r) % p
            dd = min(abs(r - s), p - abs(r - s))
            if dd == d:
                N_values.add(N_exact(r, s, p))
        if len(N_values) == 1:
            print(f"    d={d}: N = {N_values.pop()} (constant)")
        else:
            print(f"    d={d}: N varies: {sorted(N_values)}")

for p in [7, 11, 13, 17]:
    analyze_prime(p)
