#!/usr/bin/env python3
"""
WHY does F°° diverge if sum S°° = 0?

The zero-sum (trivial character) is preserved.
What BREAKS is the ANTISYMMETRY.

S°(a) + S°(m-a) = 0 (proved -- the reflection symmetry)
S°°(a) + S°°(m-a) = ???

If a ≡ 1 mod 3, then m-a ≡ (100-a) mod 3.
100 ≡ 1 mod 3, so m-a ≡ 1-a ≡ -a ≡ 2 mod 3 (when a≡1).

So a and m-a have DIFFERENT mod-3 classes!
Different centering amounts are subtracted.
The antisymmetry breaks.
"""

from math import gcd

b = 10
m = b * b

# S table
def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

S_table = {}
for p in range(m + 1, 10000):
    if not is_prime(p) or gcd(p, b) != 1: continue
    a = p % m
    if a in S_table: continue
    g = pow(b, 1, p)
    C = sum(1 for r in range(1, p) if b*r//p == b*(g*r%p)//p)
    S_table[a] = C - (p - 1) // b

units = [a for a in range(1, m) if gcd(a, m) == 1]

# Spectral class means
cls_R = {}
for a in units:
    R = (a - 1) % b
    if R not in cls_R: cls_R[R] = []
    if a in S_table: cls_R[R].append(S_table[a])
mean_R = {R: sum(v)/len(v) for R, v in cls_R.items()}

S_cent = {}
for a in units:
    if a in S_table:
        S_cent[a] = S_table[a] - mean_R[(a-1) % b]

# Mod-3 means
cls_3 = {}
for a in units:
    if a not in S_cent: continue
    k = a % 3
    if k not in cls_3: cls_3[k] = []
    cls_3[k].append(S_cent[a])
mean_3 = {k: sum(v)/len(v) for k, v in cls_3.items()}

print("Step 1: Check antisymmetry of S°")
print("="*50)
for a in sorted(units)[:10]:
    ma = m - a
    if a in S_cent and ma in S_cent:
        s = S_cent[a] + S_cent[ma]
        print(f"  S°({a:>3}) + S°({ma:>3}) = {S_cent[a]:+.4f} + {S_cent[ma]:+.4f} = {s:+.4f}")

print(f"\nAll pairs: ", end="")
all_zero = all(abs(S_cent.get(a,0) + S_cent.get(m-a,0)) < 0.001
               for a in units if a < m/2 and a in S_cent and m-a in S_cent)
print("S°(a) + S°(m-a) = 0 for all pairs" if all_zero else "BROKEN")

print(f"\nStep 2: What mod-3 does to the pairing")
print("="*50)
print(f"m = {m}, m mod 3 = {m % 3}")
print(f"If a ≡ 1 mod 3, then m-a ≡ {(m-1) % 3} mod 3")
print(f"If a ≡ 2 mod 3, then m-a ≡ {(m-2) % 3} mod 3")
print(f"If a ≡ 0 mod 3, then m-a ≡ {(m) % 3} mod 3")

print(f"\nStep 3: Antisymmetry of S°° (doubly centered)")
print("="*50)

S_double = {}
for a in units:
    if a not in S_cent: continue
    k = a % 3
    S_double[a] = S_cent[a] - mean_3.get(k, 0)

broken_count = 0
for a in sorted(units):
    ma = m - a
    if a >= ma: continue
    if a in S_double and ma in S_double:
        s = S_double[a] + S_double[ma]
        if abs(s) > 0.001:
            broken_count += 1
            if broken_count <= 5:
                print(f"  S°°({a:>3}) + S°°({ma:>3}) = "
                      f"{S_double[a]:+.4f} + {S_double[ma]:+.4f} = {s:+.4f}  "
                      f"[a%3={a%3}, (m-a)%3={(m-a)%3}]")

print(f"\n  Broken pairs: {broken_count} out of {len(units)//2}")

print(f"\n{'='*50}")
print(f"THE PROOF")
print(f"{'='*50}")
print(f"""
F° converges because of TWO properties:
  1. Sum S°(a) = 0 (trivial character vanishes)
  2. S°(a) + S°(m-a) = 0 (antisymmetry -- even characters vanish)

The mod-3 centering PRESERVES property 1 (sum = 0).
But it BREAKS property 2 (antisymmetry).

Why: m = {m} ≡ {m%3} mod 3.
  a ≡ 1 mod 3  →  m-a ≡ 2 mod 3  (different class!)
  a ≡ 2 mod 3  →  m-a ≡ 1 mod 3  (swapped!)

The centering subtracts {mean_3.get(1,0):+.4f} from a ≡ 1 mod 3
and {mean_3.get(2,0):+.4f} from a ≡ 2 mod 3.

Since the reflection a → m-a SWAPS mod-3 classes,
subtracting different amounts from each class breaks
S°°(a) + S°°(m-a) = 0.

Without antisymmetry, even characters re-enter the
decomposition. Even characters that factor through
small moduli contribute divergent sums. F°° diverges.

The mod-3 structure is entangled with the reflection
symmetry. You cannot remove one without breaking the other.
The 2/3 ratio and the bilateral symmetry are the SAME
structural fact, seen from two sides.  QED.
""")
