#!/usr/bin/env python3
"""Test: N(d, p) = floor((p-1)/d) - 1 - floor((p-1)/(2d))"""

def N_exact(d, p):
    r, s = 1, 1 + d
    count = 0
    for b in range(2, p):
        if b * r // p == b * s // p:
            count += 1
    return count

for p in [13, 23, 37, 47]:
    print(f"p = {p}:")
    for d in range(1, (p+1)//2):
        n = N_exact(d, p)
        # Various formulas
        f1 = (p-1)//d - 1 - (p-1)//(2*d)
        f2 = p//d - 1 - p//(2*d)
        f3 = (p+d-1)//(2*d) - 1  # ceil(p/(2d)) - 1
        f4 = (p-1)//(2*d)  # floor((p-1)/(2d))
        f5 = (p-d)//(2*d)  # floor((p-d)/(2d))
        match = ""
        if n == f4: match = "floor((p-1)/(2d))"
        elif n == f5: match = "floor((p-d)/(2d))"
        elif n == f3: match = "ceil(p/(2d))-1"
        if d <= 10 or n > 0:
            print(f"  d={d:>3}: N={n:>3}  (p-1)/(2d)={f4:>3}  (p-d)/(2d)={f5:>3}  {match}")
    print()
