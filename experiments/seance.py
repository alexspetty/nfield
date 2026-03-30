#!/usr/bin/env python3
"""
The seance: can we detect the factor-aligned ghosts
through their effect on CORRELATIONS between collision
counts, without computing individual C(g)?

The ghost multipliers (g ≡ 1 mod p) have C(g) = 0 when
p is DP. This creates a correlation: if g1 and g2 both
satisfy g ≡ 1 mod p, they're BOTH deranging. Their
collision counts are correlated (both zero).

The correlation between C(g1) and C(g2) should depend on
whether g1 * g2^{-1} ≡ 1 mod p. That is: the correlation
is a function of the "distance" g1/g2 in (Z/nZ)*.

If this correlation function has a peak at g1/g2 ≡ 1 mod p,
we can detect p from the correlation structure.

But here's the seance move: instead of computing C(g),
pick RANDOM r values and check for collisions. Each
(r, g) sample gives a binary observation. The correlation
across samples carries the ghost signal.

Define: X(r, g) = 1 if floor(br/n) = floor(bgr/n), else 0.
Then C(g) = Σ_r X(r, g).
And E[X] ≈ 1/b (one chance in b of same bin).

The correlation:
corr(X(r,g1), X(r,g2)) across random r
depends on whether g1/g2 creates a "resonance" with
the factor structure.
"""
import math
import random

b = 10
p, q = 7, 13
n = p * q

def collision_check(r, g, n, b):
    """Does r collide with gr at modulus n, base b?"""
    gr = g * r % n
    return b * r // n == b * gr // n

# Compute the correlation function:
# For each "distance" d = g1 * g2^{-1} mod n,
# what is the probability that if r collides at g1,
# it also collides at g2?

# Equivalently: for each d, compute
# P(X(r,g) = 1 AND X(r, gd) = 1) / P(X(r,g) = 1)

print(f"n = {p} x {q} = {n}")
print(f"\nCorrelation function: P(collide at g AND at gd | collide at g)")
print(f"{'d':>4} {'d%p':>4} {'d%q':>4} {'P(both|one)':>12} {'note':>15}")

for d in range(1, min(n, 50)):
    if math.gcd(d, n) != 1:
        continue

    both = 0
    one = 0

    for g in range(2, n):
        if math.gcd(g, n) != 1:
            continue
        gd = g * d % n
        if math.gcd(gd, n) != 1:
            continue

        for r in range(1, n):
            if math.gcd(r, n) != 1:
                continue
            x1 = collision_check(r, g, n, b)
            x2 = collision_check(r, gd, n, b)

            if x1:
                one += 1
                if x2:
                    both += 1

    cond_prob = both / one if one > 0 else 0

    note = ""
    if d % p == 1:
        note = "<-- d≡1 mod p"
    if d % q == 1:
        note = "<-- d≡1 mod q"
    if d % p == 1 and d % q == 1:
        note = "<-- d≡1 mod pq"

    if note or d <= 20:
        print(f"{d:4d} {d%p:4d} {d%q:4d} {cond_prob:12.6f} {note:>15}")
