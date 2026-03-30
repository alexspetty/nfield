#!/usr/bin/env python3
"""
Why does the anti-correlation exist?

Hypothesis: the reflection identity S(a) + S(m-a) = -1 constrains
the Fourier coefficients in a way that forces anti-correlation.

For an odd character chi: chi(m-a) = chi(-1)chi(a) = -chi(a).
So s_hat(chi) = (1/phi) sum S(a) conj(chi(a))
             = (1/phi) sum [S(a) conj(chi(a)) + S(m-a) conj(chi(m-a))]  / 2
                        (pairing a with m-a)
             = (1/phi) sum [S(a) conj(chi(a)) + (-1-S(a))(-conj(chi(a)))] / 2
             = (1/phi) sum [S(a) conj(chi(a)) + conj(chi(a)) + S(a) conj(chi(a))] / 2
             = (1/phi) sum [2 S(a) conj(chi(a)) + conj(chi(a))] / 2
             = (1/phi) sum S(a) conj(chi(a)) + (1/2phi) sum conj(chi(a))
             = s_hat(chi) + 0   (since sum chi(a) = 0 for non-trivial chi)

That's circular. Let me think differently.

What determines |s_hat(chi)|? It's the projection of S° onto chi.
S° is the centered collision deviation. Its values are integers
(or rationals) on the 40 units mod 100. The Fourier coefficients
are determined by these 40 values.

What determines |P(s, chi)|? It's the prime character sum, which
depends on how primes distribute in residue classes mod m.

The question: is there a structural reason why the characters
that S° projects onto strongly are NOT the characters that primes
project onto strongly?

Key insight: S° is a function on units mod m with specific
symmetries (antisymmetry under reflection). P is controlled by
the distribution of primes, which is approximately uniform by
Dirichlet. But "approximately uniform" means P is small for
most characters. The characters where P is LARGE are those where
the prime distribution deviates from uniform, i.e., where the
error term in the PNT for APs is large. These are the characters
whose L-functions have zeros near s.

S° is a function that reflects the additive structure of digit
bins. Its large Fourier coefficients are those that align with
the bin geometry. The bin geometry is determined by floor(br/p),
which is an additive/geometric structure.

So: large |s_hat| = character aligns with digit bin geometry
    large |P|     = character aligns with prime distribution anomalies

If digit geometry and prime anomalies are "transverse" (project onto
different characters), the anti-correlation follows.

Can we make this precise? The S values depend only on p mod m,
and specifically on the collision structure of the Beatty partition.
The partition divides {1,...,p-1} into b contiguous bins. The
collision count depends on how multiplication by b permutes these
bins. This is an additive-geometric structure.

Prime distribution anomalies (large |P|) come from zeros of
L-functions, which are multiplicative-analytic objects. There's
no known reason why the Beatty partition's Fourier spectrum should
align with the L-function zero spectrum. The anti-correlation
says they're misaligned.

This might be provable from the explicit structure of S°.
Let's look at what S°(a) actually looks like as a function of a.
"""

from math import gcd, pi, cos, sin, sqrt
from collections import defaultdict

b = 10
m = b * b

# Build S table
S_table = {}
for p in range(m + 1, 50000):
    if not (all(p % i != 0 for i in range(2, int(p**0.5)+1)) if p > 1 else False):
        continue
    if gcd(p, b) != 1: continue
    a = p % m
    if a in S_table: continue
    C = sum(1 for r in range(1, p) if b*r//p == b*(b*r%p)//p)
    S_table[a] = C - (p-1)//b

units = [a for a in range(1, m) if gcd(a, m) == 1]
phi = len(units)

cls = defaultdict(list)
for a in units:
    if a in S_table:
        cls[(a-1)%b].append(S_table[a])
mean_R = {R: sum(v)/len(v) for R, v in cls.items()}

S_cent = {}
for a in units:
    if a in S_table:
        S_cent[a] = S_table[a] - mean_R[(a-1)%b]

# Print S° values
print("S° values on units mod 100:")
print(f"{'a':>4} {'S(a)':>5} {'S°(a)':>6} {'a mod 3':>7} {'R':>3}")
for a in sorted(units):
    if a in S_table:
        print(f"{a:>4} {S_table[a]:>5} {S_cent[a]:>+6.1f} {a%3:>7} {(a-1)%b:>3}")

# The S° function on 40 units: what does its Fourier spectrum look like?
# Plot |s_hat|^2 as a function of character index
print("\n\nFourier spectrum |s_hat|^2:")

# Use primitive root mod 25 (g=2) and mod 4 (g=3)
g25 = 2
dlog25 = {}
val = 1
for i in range(20):
    dlog25[val] = i
    val = val * g25 % 25
dlog4 = {1: 0, 3: 1}

print(f"{'j':>2} {'k':>3} {'|sh|^2':>10} {'odd':>4}")
for j in range(2):
    for k in range(20):
        chi = {}
        for a in range(100):
            if gcd(a, 100) != 1:
                chi[a] = 0
            else:
                angle = pi*j*dlog4[a%4] + 2*pi*k*dlog25[a%25]/20
                chi[a] = complex(cos(angle), sin(angle))

        is_odd = abs(chi[99] - (-1)) < 1e-6

        s_hat = sum(S_cent.get(a,0) * chi[a].conjugate()
                    for a in units) / phi
        mag2 = abs(s_hat)**2

        if is_odd and mag2 > 1e-10:
            print(f"{j:>2} {k:>3} {mag2:>10.6f} {'ODD' if is_odd else 'even':>4}")

# Now: look at the STRUCTURE of S° more carefully.
# S° on the 40 units. Can we express it in a simple form?
print("\n\nS° by spectral class R and within-class position:")
for R in range(b):
    vals = [(a, S_cent[a]) for a in sorted(units) if (a-1)%b == R and a in S_cent]
    if not vals: continue
    print(f"R={R}: {[(a, f'{v:+.1f}') for a, v in vals]}")

# Key question: is the spectrum of S° determined by a simple
# structural feature (like the slice formula)?
# The finite determination formula: S(a) = -1 - floor(a/b) + sum_{n in G} d_n(a)
# where d_n(a) = floor((n+1)a/m) - floor(na/m)
# The Fourier transform of floor functions has known structure...
print("\n\nS(a) from the slice formula:")
G = [n for n in range(m) if n // (b) == n % b]  # good slices for lag 1
print(f"Good slices G (|G|={len(G)}): {G[:20]}...")

for a in [1, 3, 7, 9, 11]:
    s_val = -1 - a // b
    for n in G:
        s_val += ((n+1)*a) // m - (n*a) // m
    print(f"  S({a}) = {s_val} (table: {S_table.get(a, '?')})")
