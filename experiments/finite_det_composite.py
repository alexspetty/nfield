#!/usr/bin/env python3
"""
Does finite determination hold at composites?

For a prime p, S_1(p) depends only on p mod b^2.
For a composite n, does C(b mod n) - floor((n-1)/b)
equal C(b mod p') - floor((p'-1)/b) when p' ≡ n mod b^2?
"""
import math

b = 10
m = b * b  # 100

def collision_at(n, g):
    """C(g) at modulus n."""
    return sum(1 for r in range(1, n)
               if math.gcd(r, n) == 1
               and b * r // n == b * (g * r % n) // n)

# Pick a composite
n = 77  # 7 * 11
a = n % m  # 77
g = b % n  # 10

C_composite = collision_at(n, g)
Q_composite = (n - 1) // b
S_composite = C_composite - Q_composite

print(f"Composite n = {n}, n mod {m} = {a}")
print(f"C(b mod n) = {C_composite}, Q = {Q_composite}, S = {S_composite}")
print(f"phi(n) = {sum(1 for r in range(1,n) if math.gcd(r,n)==1)}")

# Find primes p ≡ 77 mod 100
print(f"\nPrimes p ≡ {a} mod {m}:")
for p in range(a, 2000, m):
    if p < 2:
        continue
    if any(p % i == 0 for i in range(2, int(p**0.5) + 1)):
        continue
    C_prime = collision_at(p, b % p)
    Q_prime = (p - 1) // b
    S_prime = C_prime - Q_prime
    print(f"  p = {p}: C = {C_prime}, Q = {Q_prime}, S = {S_prime}")

# Try another composite
print()
n = 91  # 7 * 13
a = n % m
g = b % n

C_composite = collision_at(n, g)
Q_composite = (n - 1) // b
S_composite = C_composite - Q_composite

print(f"Composite n = {n}, n mod {m} = {a}")
print(f"C(b mod n) = {C_composite}, Q = {Q_composite}, S = {S_composite}")

print(f"\nPrimes p ≡ {a} mod {m}:")
for p in range(a, 2000, m):
    if p < 2:
        continue
    if any(p % i == 0 for i in range(2, int(p**0.5) + 1)):
        continue
    C_prime = collision_at(p, b % p)
    Q_prime = (p - 1) // b
    S_prime = C_prime - Q_prime
    print(f"  p = {p}: C = {C_prime}, Q = {Q_prime}, S = {S_prime}")
