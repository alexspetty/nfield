#!/usr/bin/env python3
"""Check if N(r,s) depends only on distance, or also on position."""

def N_exact(r, s, p):
    count = 0
    for b in range(2, p):
        if b * r // p == b * s // p:
            count += 1
    return count

p = 13
print(f"p = {p}: checking ALL pairs at each distance\n")

for d in range(1, (p+1)//2):
    N_values = {}
    for r in range(1, p):
        s = (r + d) % p
        if s == 0: s = p  # shouldn't happen for prime p
        if s > p - 1: continue
        n = N_exact(r, s if s > 0 else p, p)
        if n not in N_values:
            N_values[n] = []
        N_values[n].append((r, s))

    if len(N_values) == 1:
        val = list(N_values.keys())[0]
        print(f"  d={d}: N = {val} (constant across all {sum(len(v) for v in N_values.values())} pairs)")
    else:
        print(f"  d={d}: N VARIES:")
        for n_val in sorted(N_values.keys()):
            pairs = N_values[n_val]
            print(f"    N={n_val}: {len(pairs)} pairs, e.g. {pairs[:3]}")
