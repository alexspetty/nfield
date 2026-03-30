#!/usr/bin/env python3
"""
The lag signature: S_ell(n) across multiple lags.

For composite n vs prime n', how does the lag signature differ?

Key insight: S_ell depends on n mod b^{ell+1}. For small n,
n mod b^{ell+1} = n for ell >= 1 (when b^{ell+1} > n).
So higher lags don't give new information for small n.

For LARGE n, higher lags give genuinely new information
because n mod b^{ell+1} is different from n mod b^ell.

But wait: we KNOW n. So n mod b^{ell+1} is known for all ell.
The collision invariant S_ell is determined by this residue.
We can compute the decomposition theorem at every lag, getting
L-values for characters at every modulus b^{ell+1}.

The question: do these L-values constrain the factorization?
"""
import math

b = 10

def collision_at_lag(n, ell):
    """S_ell(n) = C(b^ell mod n) - floor((n-1)/b^ell)"""
    if n <= 1:
        return 0
    g = pow(b, ell, n)
    C = 0
    bl = b ** ell
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        d1 = bl * r // n
        gr = g * r % n
        d2 = bl * gr // n
        if d1 == d2:
            C += 1
    Q = (n - 1) // bl if bl <= n else 0
    return C - Q

# Compare lag signatures for several composites and primes
print("Lag signatures (S_1, S_2, S_3):")
print(f"{'n':>6} {'type':>10} {'S_1':>5} {'S_2':>5} {'S_3':>5}")

test_ns = [
    (77, "7x11"),
    (91, "7x13"),
    (143, "11x13"),
    (221, "13x17"),
    (71, "prime"),
    (73, "prime"),
    (79, "prime"),
    (83, "prime"),
    (89, "prime"),
    (97, "prime"),
    (101, "prime"),
    (103, "prime"),
    (107, "prime"),
    (109, "prime"),
    (113, "prime"),
    (127, "prime"),
    (131, "prime"),
    (137, "prime"),
    (139, "prime"),
    (149, "prime"),
    (151, "prime"),
]

for n, label in test_ns:
    s1 = collision_at_lag(n, 1)
    s2 = collision_at_lag(n, 2)
    s3 = collision_at_lag(n, 3)
    print(f"{n:6d} {label:>10} {s1:>5d} {s2:>5d} {s3:>5d}")

# Key question: is S_2 = 0 a signature of compositeness?
print(f"\nS_2 = 0 test:")
composites_with_s2_zero = 0
primes_with_s2_zero = 0
for n in range(11, 300):
    is_prime = all(n % i != 0 for i in range(2, int(n**0.5)+1))
    if math.gcd(n, b) != 1:
        continue
    s2 = collision_at_lag(n, 2)
    if s2 == 0:
        if is_prime:
            primes_with_s2_zero += 1
        else:
            composites_with_s2_zero += 1

print(f"  Composites with S_2 = 0: {composites_with_s2_zero}")
print(f"  Primes with S_2 = 0: {primes_with_s2_zero}")
