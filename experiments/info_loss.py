#!/usr/bin/env python3
"""
Trace EXACTLY where information is lost during multiplication.

Start with r. We know everything about r:
  - r mod p (its p-component)
  - r mod q (its q-component)
  - floor(br/p) (its p-digit)
  - floor(br/q) (its q-digit)
  - floor(br/n) (its composite digit)

Multiply by g to get gr mod n.
  - gr mod p = g*r mod p (independent)
  - gr mod q = g*r mod q (independent)
  - floor(b*gr/p) (its new p-digit)
  - floor(b*gr/q) (its new q-digit)
  - floor(b*gr/n) (its new composite digit)

A collision at the composite means floor(br/n) = floor(b*gr/n).

WHERE is information lost?

Step 1: r -> (r_p, r_q)           CRT decomposition. LOSSLESS.
Step 2: (r_p, r_q) -> (d_p, d_q)  Digit extraction. LOSSY.
         Each floor(br_p/p) maps ~p/b residues to one digit.
Step 3: (d_p, d_q) -> d_n          Interleaving. LOSSY.
         f(d_p, d_q) has column collisions.

Multiplication acts on Step 1: (r_p, r_q) -> (gr_p, gr_q).
This is independent on each component.

Collision detection happens at Step 3: d_n = d_n'.

Information is lost at TWO stages:
  Step 2: residues -> digits (many-to-one per prime)
  Step 3: digit pairs -> composite digit (column collisions)

The question: which stage loses the factoring information?
"""
import math

b = 10
p, q = 7, 13
n = p * q

def modinv(a, m):
    g, x = 0, 1
    a0, m0 = a % m, m
    while a0 != 0:
        qq = m0 // a0
        m0, a0 = a0, m0 - qq * a0
        g, x = x, g - qq * x
    return g % m

qi = modinv(q, p)
pi = modinv(p, q)

def crt(rp, rq):
    return (rp * q * qi + rq * p * pi) % n

g = 2  # test multiplier

print(f"n = {p} x {q} = {n}, g = {g}\n")
print(f"{'r':>4} {'rp':>3} {'rq':>3} {'dp':>3} {'dq':>3} {'dn':>3} | "
      f"{'gr':>4} {'grp':>3} {'grq':>3} {'dp2':>3} {'dq2':>3} {'dn2':>3} | "
      f"{'Cp':>3} {'Cq':>3} {'Cn':>3} {'ghost':>5}")

# Track information at each stage
stage2_collisions = 0  # same (d_p, d_q) after multiplication
stage3_collisions = 0  # same d_n after multiplication
ghost_count = 0

for rp in range(1, p):
    for rq in range(1, q):
        r = crt(rp, rq)
        if math.gcd(r, n) != 1:
            continue

        gr = g * r % n
        grp = gr % p
        grq = gr % q

        dp = b * rp // p
        dq = b * rq // q
        dn = b * r // n

        dp2 = b * grp // p
        dq2 = b * grq // q
        dn2 = b * gr // n

        coll_p = (dp == dp2)
        coll_q = (dq == dq2)
        coll_n = (dn == dn2)
        ghost = coll_n and not (coll_p and coll_q)

        if coll_p and coll_q:
            stage2_collisions += 1
        if coll_n:
            stage3_collisions += 1
        if ghost:
            ghost_count += 1

        # Print interesting cases
        if coll_n:
            print(f"{r:4d} {rp:3d} {rq:3d} {dp:3d} {dq:3d} {dn:3d} | "
                  f"{gr:4d} {grp:3d} {grq:3d} {dp2:3d} {dq2:3d} {dn2:3d} | "
                  f"{'=' if coll_p else '.':>3} {'=' if coll_q else '.':>3} {'=' :>3} "
                  f"{'GHOST' if ghost else '':>5}")

print(f"\nStage 2 collisions (both primes): {stage2_collisions}")
print(f"Stage 3 collisions (composite): {stage3_collisions}")
print(f"Ghosts (stage 3 only): {ghost_count}")

# NOW: for each ghost, what EXACTLY happened?
print(f"\n--- Ghost anatomy ---")
print(f"For each ghost: what changed at each stage?\n")

for rp in range(1, p):
    for rq in range(1, q):
        r = crt(rp, rq)
        if math.gcd(r, n) != 1:
            continue

        gr = g * r % n
        grp = gr % p
        grq = gr % q

        dp = b * rp // p
        dq = b * rq // q
        dn = b * r // n

        dp2 = b * grp // p
        dq2 = b * grq // q
        dn2 = b * gr // n

        coll_p = (dp == dp2)
        coll_q = (dq == dq2)
        coll_n = (dn == dn2)
        ghost = coll_n and not (coll_p and coll_q)

        if ghost:
            # The digits changed at p or q, but the composite digit didn't
            # This means (dp, dq) -> (dp2, dq2) but f(dp,dq) = f(dp2,dq2)
            print(f"  r={r:3d}: ({dp},{dq})->d={dn}   "
                  f"gr={gr:3d}: ({dp2},{dq2})->d={dn2}   "
                  f"dp {'changed' if dp!=dp2 else 'same':>8}  "
                  f"dq {'changed' if dq!=dq2 else 'same':>8}")
