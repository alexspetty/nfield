#!/usr/bin/env python3
"""
Can we detect ghost collisions cheaply?

A ghost collision at (r_p, r_q) under multiplier g means:
- floor(b*r/n) = floor(b*gr/n)       [collision at composite]
- floor(b*r_p/p) != floor(b*g*r_p/p) [no collision at p]
  OR floor(b*r_q/q) != floor(b*g*r_q/q) [no collision at q]

The ghost exists because the interleaving function f has
column collisions. Two different (d_p, d_q) pairs map to
the same composite digit.

KEY OBSERVATION: If we could detect whether a specific r
is involved in a ghost collision WITHOUT knowing p and q,
we'd have factoring information.

But: to check floor(b*r/n) = floor(b*gr/n), we only need
n (which we know) and r (which we choose). The collision
check is O(1) per r.

The full C(g) requires checking all r from 1 to n-1: O(n).

But what if we sample? Pick random r's and check for
collisions. The collision rate at each g encodes the
factoring information.

Even better: the DERANGING multipliers have C(g) = 0.
Finding a deranging g proves that c = b(1-g)^{-1} mod n
is in {1,...,b-1}. The set of deranging c's at the composite
is the intersection of the deranging c's at p and q.

If we could find ALL b-1 deranging g's, we'd know which
c values in {1,...,b-1} are deranging. The missing values
(c's that are deranging at one prime but not the other)
encode the factorization.

COST: Finding each deranging g requires verifying C(g)=0,
which naively costs O(n). But C(g)=0 means NO r collides.
We can DISPROVE C(g)=0 by finding a single collision: O(1)
expected time if C(g) is large. So non-deranging g's are
cheap to identify.

The expensive case: proving C(g) = 0 (no collision exists).
That requires checking all r. Unless there's a shortcut.

THE SHORTCUT IDEA: For prime n, C(g) = 0 iff
c = b(1-g)^{-1} mod n is in {1,...,b-1}. This is O(log n).
For COMPOSITE n, is the same criterion sufficient?
"""
import math

b = 10

def is_deranging_prime(g, p, b):
    """For prime p: C(g)=0 iff c = b(1-g)^{-1} mod p in {1,...,b-1}."""
    if g % p == 1:
        return False
    c = (b * pow(1 - g, -1, p)) % p
    return 1 <= c <= b - 1

def is_deranging_composite_direct(g, n, b):
    """Direct check: C(g) = 0 at composite n."""
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        if b * r // n == b * (g * r % n) // n:
            return False
    return True

def is_deranging_composite_criterion(g, n, b):
    """Test: does the c-criterion work at composites?"""
    if math.gcd(1 - g, n) != 1:
        return False
    c = (b * pow(1 - g, -1, n)) % n
    return 1 <= c <= b - 1

p, q = 7, 13
n = p * q

print(f"n = {p} x {q} = {n}")
print(f"Testing c-criterion at composite:\n")
print(f"{'g':>4} {'c':>4} {'criterion':>10} {'direct':>8} {'match':>6}")

mismatches = 0
for g in range(2, n):
    if math.gcd(g, n) != 1:
        continue
    crit = is_deranging_composite_criterion(g, n, b)
    direct = is_deranging_composite_direct(g, n, b)
    match = crit == direct

    if not match:
        c = (b * pow(1 - g, -1, n)) % n if math.gcd(1-g, n) == 1 else -1
        print(f"{g:4d} {c:4d} {str(crit):>10} {str(direct):>8} {'YES' if match else 'NO':>6}")
        mismatches += 1

if mismatches == 0:
    print("ALL MATCH. The c-criterion works at composites.")
else:
    print(f"\n{mismatches} mismatches found.")

# If it works, then finding deranging g's is O(log n) each
# And the deranging c-set encodes factoring information
print(f"\nDeranging c-set at n={n}: ", end="")
c_set = []
for g in range(2, n):
    if math.gcd(g, n) != 1:
        continue
    if is_deranging_composite_criterion(g, n, b):
        c = (b * pow(1 - g, -1, n)) % n
        if c not in c_set:
            c_set.append(c)
print(sorted(c_set))

print(f"Deranging c-set at p={p}: ", end="")
c_p = sorted(set((b * pow(1 - g, -1, p)) % p
              for g in range(2, p) if math.gcd(1-g, p) == 1
              and 1 <= (b * pow(1-g, -1, p)) % p <= b-1))
print(c_p)

print(f"Deranging c-set at q={q}: ", end="")
c_q = sorted(set((b * pow(1 - g, -1, q)) % q
              for g in range(2, q) if math.gcd(1-g, q) == 1
              and 1 <= (b * pow(1-g, -1, q)) % q <= b-1))
print(c_q)

# The factoring signal
missing = [c for c in range(1, b) if c in c_p and c in c_q and c not in c_set]
extra = [c for c in c_set if c not in c_p or c not in c_q]
print(f"\nIntersection of prime c-sets: {sorted(set(c_p) & set(c_q))}")
print(f"Composite c-set: {sorted(c_set)}")
print(f"Missing from intersection: {missing}")
print(f"Extra in composite: {extra}")
