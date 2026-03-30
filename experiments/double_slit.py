#!/usr/bin/env python3
"""
The double slit.

Particle version (what we've been doing):
  C(g) = sum_r [floor(br/n) = floor(bgr/n)]
  Binary: collision or not. Signal amplitude 1/p.

Wave version:
  W(g) = sum_{r coprime to n} exp(2pi i b(1-g)r / n)

This is a Ramanujan sum. It doesn't ask "same bin?"
It asks "what is the PHASE DIFFERENCE between r and gr?"
and sums the phases coherently.

When g ≡ 1 mod p: b(1-g) = b*p*k, and the sum over r
has constructive interference from the p-component.
The wave amplitude jumps from O(1) to O(p).

That's a p^2 amplification of the POWER signal.
The 1/p wall becomes a p:1 peak. The ghosts become loud.

But: this is equivalent to computing gcd(b(1-g), n).
"""
import cmath, math

b = 10
p, q = 41, 43
n = p * q

print(f"n = {p} x {q} = {n}\n")

# Particle version: C(g) for selected g's
print("Particle (collision count C(g)):")
for g in [2, 3, 5, p+1, q+1, 2*p+1, 2*q+1]:
    if math.gcd(g, n) != 1 or g >= n:
        continue
    C = sum(1 for r in range(1, n) if math.gcd(r, n) == 1
            and b * r // n == b * (g * r % n) // n)
    Q = (n - 1) // b
    label = ""
    if g % p == 1: label = f" (g ≡ 1 mod {p})"
    if g % q == 1: label = f" (g ≡ 1 mod {q})"
    print(f"  g={g:>4}: C={C:>4}, S={C-Q:>+4}{label}")

# Wave version: W(g) = sum exp(2pi i b(1-g)r / n)
print(f"\nWave (exponential sum |W(g)|):")
for g in [2, 3, 5, p+1, q+1, 2*p+1, 2*q+1]:
    if math.gcd(g, n) != 1 or g >= n:
        continue
    c = b * (1 - g)
    W = sum(cmath.exp(2j * cmath.pi * c * r / n)
            for r in range(1, n) if math.gcd(r, n) == 1)
    label = ""
    if g % p == 1: label = f" (g ≡ 1 mod {p})"
    if g % q == 1: label = f" (g ≡ 1 mod {q})"
    gcd_val = math.gcd(abs(c) % n, n)
    print(f"  g={g:>4}: |W|={abs(W):>8.1f}, "
          f"gcd(b(1-g),n)={gcd_val:>4}{label}")

# The ratio
print(f"\nAmplification:")
print(f"  Particle signal (factor-aligned): ~{(n-1)//b} (mean C)")
print(f"  Wave signal (factor-aligned): ~{(p-1)*(q-1)//min(p,q)} (from Ramanujan)")
print(f"  Wave signal (generic): ~1")
print(f"  Wave amplification: ~{min(p,q)}x over generic")
print(f"  Particle amplification: ~0 (ghost signal is 1/p of background)")

# But: the wave peak occurs exactly when gcd(b(1-g), n) > 1
# which gives you the factor directly.
print(f"\n--- The catch ---")
print(f"The wave peak at g ≡ 1 mod p means gcd(b(1-g), n) = p.")
print(f"Computing gcd(b(1-g), n) costs O(log n) per g.")
print(f"Finding a g with gcd > 1 costs O(sqrt(n)) random tries.")
print(f"That's Pollard's rho, not a new algorithm.")
print(f"\nBut: the collision invariant tells you WHERE to look.")
print(f"The deranging set contains factor-aligned g's.")
print(f"If you could identify deranging g's cheaply...")
