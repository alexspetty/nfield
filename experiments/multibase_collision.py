#!/usr/bin/env python3
"""
Compute the full collision portrait C_p(g, b) for a small prime p
across many bases. Look for base-independent structure.
"""

def collision_count(g, p, b):
    count = 0
    for r in range(1, p):
        d_r = b * r // p
        gr = (g * r) % p
        d_gr = b * gr // p
        if d_r == d_gr:
            count += 1
    return count

def show_prime(p):
    print(f"\n{'='*60}")
    print(f"Prime p = {p}, group order = {p-1}")
    print(f"{'='*60}")

    bases = list(range(2, p))
    mults = list(range(1, p))

    # Print header
    print(f"\n{'g':>4}", end="")
    for b in bases:
        print(f"  b={b:>2}", end="")
    print("   | row sum  | even?")

    for g in mults:
        print(f"{g:>4}", end="")
        row = []
        for b in bases:
            c = collision_count(g, p, b)
            row.append(c)
            print(f"  {c:>4}", end="")
        rsum = sum(row)
        all_even = all(c % 2 == 0 for c in row)
        print(f"   | {rsum:>6}  | {'Y' if all_even else 'N'}")

    # Column sums
    print(f"\nsum ", end="")
    for b in bases:
        csum = sum(collision_count(g, p, b) for g in mults)
        print(f"  {csum:>4}", end="")
    print()

    # Column sums minus (p-1) (removing g=1 contribution)
    print(f"S=C-Q", end="")
    for b in bases:
        total_S = 0
        Q = (p - 1) // b
        for g in range(2, p):
            c = collision_count(g, p, b)
            total_S += (c - Q)
        print(f"  {total_S:>4}", end="")
    print()

    # Check: is there a g that's deranging (C=0) in ALL bases?
    print(f"\nDeranging in all bases:")
    for g in range(2, p):
        deranging_bases = [b for b in bases if collision_count(g, p, b) == 0]
        if len(deranging_bases) > 1:
            print(f"  g={g}: deranging in bases {deranging_bases}")

    # The "shape" - normalize C(g,b) by dividing by Q
    print(f"\nNormalized C(g,b)/Q:")
    print(f"{'g':>4}", end="")
    for b in bases:
        print(f"  b={b:>2}", end="")
    print()
    for g in range(2, min(p, 8)):
        print(f"{g:>4}", end="")
        for b in bases:
            c = collision_count(g, p, b)
            Q = (p - 1) // b
            ratio = c / Q if Q > 0 else 0
            print(f"  {ratio:>.2f}", end="")
        print()

show_prime(7)
show_prime(13)
show_prime(11)
