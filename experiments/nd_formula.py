#!/usr/bin/env python3
"""Find the exact formula for N(d, p)."""

def N_exact(d, p):
    """Count bases b in {2,...,p-1} where two points at distance d share a bin."""
    count = 0
    r, s = 1, 1 + d  # any pair at distance d
    for b in range(2, p):
        if b * r // p == b * s // p:
            count += 1
    return count

for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
    print(f"p = {p}:")
    vals = []
    for d in range(1, (p+1)//2):
        n = N_exact(d, p)
        vals.append(n)
        # Try formulas
        f1 = (p - 1) // d - 2  # floor((p-1)/d) - 2
        f2 = (p - 1) // d - 1  # floor((p-1)/d) - 1
        f3 = p // d - 2        # floor(p/d) - 2
        match = ""
        if n == f1: match = "= floor((p-1)/d)-2"
        elif n == f2: match = "= floor((p-1)/d)-1"
        elif n == f3: match = "= floor(p/d)-2"
        if d <= 8 or n > 0:
            print(f"  d={d:>3}: N={n:>4}  floor(p/d)-2={f3:>4}  floor((p-1)/d)-2={f1:>4}  {match}")
    print()
