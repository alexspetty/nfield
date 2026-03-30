#!/usr/bin/env python3
"""
Why are ghost collisions ~100%?

At a prime p, the mean collision count is C_mean ≈ (p-1)/b.
The collision probability per (r, g) pair is ≈ 1/b.

At the composite n = pq, C_mean ≈ (n-1)/b ≈ pq/b.

For the tensor case (both primes collide independently):
- Prob(collision at p) per r ≈ 1/b
- Prob(collision at q) per r ≈ 1/b
- If independent: Prob(both) ≈ 1/b²

So tensor collision count ≈ phi(n)/b² = (p-1)(q-1)/b²
And composite collision count ≈ phi(n)/b = (p-1)(q-1)/b

Ratio: tensor/composite ≈ 1/b

For b=10: tensor is ~10% of composite. But we measured
it as ~0%. So the independence assumption overcounts
the tensor contribution. The actual tensor rate is even
LOWER than 1/b².

Why? Because both primes being DP (p=7, q=11 in base 10)
means ZERO collisions at each prime individually. For DP
primes, C(g) = 0 for ALL g (that's the digit-partitioning
property). So tensor = 0 exactly.

Wait. p=7 and q=11 are both DP in base 10 (both ≤ 11 = b+1).
So at each prime individually, there are NO collisions for
any multiplier. The tensor contribution is exactly 0.
That's why ghost/composite = 100%.

For composites where BOTH primes are DP, ALL collisions
are ghosts. The ghosts come from the interleaving.

What about composites with non-DP primes?
"""
import math

b = 10

def is_dp(p, b):
    return p <= b + 1

# Recompute with explicit DP check
composites = [
    (7, 11),   # both DP
    (7, 13),   # 7 DP, 13 not
    (11, 13),  # 11 DP, 13 not
    (13, 17),  # neither DP
    (13, 19),  # neither DP
    (17, 19),  # neither DP
    (23, 29),  # neither DP, larger
]

def modinv(a, m):
    g, x = 0, 1
    a0, m0 = a % m, m
    while a0 != 0:
        q = m0 // a0
        m0, a0 = a0, m0 - q * a0
        g, x = x, g - q * x
    return g % m

for p, q in composites:
    n = p * q
    qi = modinv(q, p)
    pi = modinv(p, q)

    def crt(rp, rq):
        return (rp * q * qi + rq * p * pi) % n

    dp_p = is_dp(p, b)
    dp_q = is_dp(q, b)

    # Sample a few multipliers
    ghost_total = 0
    comp_total = 0
    tens_total = 0
    count = 0

    for g in range(2, min(n, 200)):
        if math.gcd(g, n) != 1:
            continue
        count += 1

        for rp in range(1, p):
            for rq in range(1, q):
                r = crt(rp, rq)
                if math.gcd(r, n) != 1:
                    continue

                gr = g * r % n
                grp, grq = gr % p, gr % q

                dp = b * rp // p
                dq = b * rq // q
                dp2 = b * grp // p
                dq2 = b * grq // q

                d_n = b * r // n
                d_n2 = b * gr // n

                coll_p = (dp == dp2)
                coll_q = (dq == dq2)
                coll_n = (d_n == d_n2)

                if coll_n:
                    comp_total += 1
                if coll_p and coll_q:
                    tens_total += 1
                if coll_n and not (coll_p and coll_q):
                    ghost_total += 1

    if count == 0:
        continue

    mc = comp_total / count
    mt = tens_total / count
    mg = ghost_total / count
    gf = mg / mc if mc > 0 else 0

    print(f"{p:>3}x{q:<3} = {n:>5}  "
          f"DP=({'+' if dp_p else '-'},{'+' if dp_q else '-'})  "
          f"C={mc:7.1f}  tensor={mt:6.1f}  ghost={mg:7.1f}  "
          f"ghost% = {100*gf:5.1f}%  "
          f"1/b = {100/b:5.1f}%")
