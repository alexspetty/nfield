#!/usr/bin/env python3
"""
The SHAPE of C(g) as a function of g.

At a prime p: C(g) has a specific distribution over g.
At a composite n = pq: C(g) has a different distribution
(dominated by ghost collisions).

What statistical property of the SHAPE distinguishes
composites from primes?

Key insight: at a prime p, the collision function is
determined by the bin structure of floor(br/p). The
distribution of C(g) values depends on the spectral
structure (eigenvalues of the cross-alignment matrix).

At a composite, the ghost collisions create additional
C > 0 values. The distribution shifts.

Question: is the VARIANCE of C(g) different at composites
vs primes? The variance is computable from sum C(g)^2,
which is related to the Parseval sum.
"""
import math

b = 10

def C_all(n):
    """Compute C(g) for all coprime g."""
    vals = []
    for g in range(2, n):
        if math.gcd(g, n) != 1:
            continue
        c = sum(1 for r in range(1, n) if math.gcd(r,n)==1
                and b*r//n == b*(g*r%n)//n)
        vals.append(c)
    return vals

# Compare distributions
targets = [
    (91, "7x13"),
    (77, "7x11"),
    (89, "prime"),
    (97, "prime"),
    (83, "prime"),
    (79, "prime"),
]

print(f"Distribution of C(g) values:\n")
print(f"{'n':>5} {'type':>6} {'mean':>7} {'var':>8} {'zeros':>6} "
      f"{'max':>5} {'skew':>7}")

for n, label in targets:
    vals = C_all(n)
    mean = sum(vals) / len(vals)
    var = sum((v - mean)**2 for v in vals) / len(vals)
    zeros = sum(1 for v in vals if v == 0)
    mx = max(vals)

    # Skewness
    std = var ** 0.5
    if std > 0:
        skew = sum((v - mean)**3 for v in vals) / (len(vals) * std**3)
    else:
        skew = 0

    print(f"{n:5d} {label:>6} {mean:7.2f} {var:8.2f} {zeros:6d} "
          f"{mx:5d} {skew:7.3f}")

# The variance relates to sum C(g)^2.
# By Parseval: sum |c_hat(chi)|^2 = (1/phi) sum |C(g)|^2
# And by the bin identity: c_hat(chi) = (1/phi) sum |A_d|^2
# So sum_chi (sum_d |A_d(chi)|^2)^2 = sum_g C(g)^2
#
# This connects the shape of C(g) to the fourth moment
# of the bin character sums.
