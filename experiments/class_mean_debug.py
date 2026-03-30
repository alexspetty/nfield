#!/usr/bin/env python3
"""
Investigate why the class mean formula fails for composite bases.
Look at the actual distribution of mc mod p vs mb for specific primes.
"""

def isprime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def compute_S_and_details(b, p):
    """Compute S via sawtooth with correct c."""
    g = pow(b, 1, p)  # lag 1, g = b mod p
    one_minus_g = (1 - g) % p
    c = (b * pow(one_minus_g, p - 2, p)) % p
    Q = (p - 1) // b

    pos = 0
    neg = 0
    for m in range(1, Q + 1):
        mc = (m * c) % p
        mb = m * b
        if mc > mb:
            pos += 1
        elif mc < mb:
            neg += 1

    S = pos - neg
    return S, pos, neg, Q, c

# For base 10, look at R=0 and R=8 primes
b = 10
print(f"BASE {b}")
print(f"{'p':>8} {'R':>3} {'Q':>4} {'c':>6} {'c/p':>8} {'pos':>5} {'neg':>5} {'S':>5} {'equid':>8}")

for p in range(b + 2, 500):
    if not isprime(p) or p % b == 0:
        continue
    R = (p - 1) % b
    if R not in [0, 8]:
        continue
    S, pos, neg, Q, c = compute_S_and_details(b, p)
    equid = (R + 1 - b) / b
    print(f"{p:>8} {R:>3} {Q:>4} {c:>6} {c/p:>8.4f} {pos:>5} {neg:>5} {S:>5} {equid:>8.3f}")

# Compare: base 3
print(f"\nBASE 3")
b = 3
print(f"{'p':>8} {'R':>3} {'Q':>4} {'c':>6} {'c/p':>8} {'pos':>5} {'neg':>5} {'S':>5} {'equid':>8}")

for p in range(b + 2, 500):
    if not isprime(p) or p % b == 0:
        continue
    R = (p - 1) % b
    S, pos, neg, Q, c = compute_S_and_details(b, p)
    equid = (R + 1 - b) / b
    print(f"{p:>8} {R:>3} {Q:>4} {c:>6} {c/p:>8.4f} {pos:>5} {neg:>5} {S:>5} {equid:>8.3f}")
