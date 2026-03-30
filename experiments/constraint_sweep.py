#!/usr/bin/env python3
"""
The constraint sweep: do structural identities at
multiple bases jointly determine the factorization?

For n = 91 = 7 x 13, compute A_d at bases 3, 7, 11.
At each base, extract: magnitudes, phases, reflection
constraints, sum constraints.

Then: given ONLY the magnitudes and structural constraints
across all bases, is there a unique (p, q) consistent
with them?

Test: for each candidate factorization p' * q' = 91
(only 7 * 13), and for several n' near 91 that are
prime, check whether the magnitude + constraint data
distinguishes them.
"""
import cmath, math

def compute_Ad(n, base, j_func):
    """
    Compute A_d for a character given by j_func(r) -> chi(r).
    j_func should return chi(r) for coprime r, 0 otherwise.
    """
    b = base
    bins = [[] for _ in range(b)]
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        d = b * r // n
        if d >= b:
            d = b - 1
        bins[d].append(r)

    A = []
    for d in range(b):
        Ad = sum(j_func(r) for r in bins[d])
        A.append(Ad)
    return A

# For composite n = 91, use character chi_p[j7] x chi_q[j13]
def make_composite_chi(n, p, q, j7, j13):
    g7 = next(c for c in range(2, p) if all(pow(c, k, p) != 1 for k in range(1, p-1)))
    g13 = next(c for c in range(2, q) if all(pow(c, k, q) != 1 for k in range(1, q-1)))

    dl7 = {}; v = 1
    for k in range(p-1): dl7[v] = k; v = v * g7 % p
    dl13 = {}; v = 1
    for k in range(q-1): dl13[v] = k; v = v * g13 % q

    w7 = cmath.exp(2j * cmath.pi / (p-1))
    w13 = cmath.exp(2j * cmath.pi / (q-1))

    def chi(r):
        if math.gcd(r, n) != 1:
            return 0
        return w7**(j7 * dl7[r % p]) * w13**(j13 * dl13[r % q])
    return chi

# For prime n, use a character mod n
def make_prime_chi(n, j):
    g = next(c for c in range(2, n) if all(pow(c, k, n) != 1 for k in range(1, n-1)))
    dl = {}; v = 1
    for k in range(n-1): dl[v] = k; v = v * g % n
    w = cmath.exp(2j * cmath.pi / (n-1))

    def chi(r):
        if math.gcd(r, n) != 1:
            return 0
        return w**(j * dl[r])
    return chi

p, q = 7, 13
n = p * q  # 91

bases = [3, 7, 11, 13]
# Remove bases that divide n
bases = [b for b in bases if math.gcd(b, n) == 1]

j7, j13 = 2, 5
chi_91 = make_composite_chi(n, p, q, j7, j13)

print(f"n = {p} x {q} = {n}")
print(f"Character: chi_p[{j7}] x chi_q[{j13}]")
print(f"Bases: {bases}\n")

# Collect magnitude fingerprints at each base
fingerprint_91 = {}
for base in bases:
    A = compute_Ad(n, base, chi_91)
    mags = tuple(round(abs(a), 6) for a in A)
    phases = tuple(round(cmath.phase(a), 4) for a in A)

    # Check reflection: A_{b-1-d} should be conj(-A_d) for odd chi
    reflection_ok = True
    for d in range(base // 2):
        d2 = base - 1 - d
        diff = abs(abs(A[d]) - abs(A[d2]))
        if diff > 0.01:
            reflection_ok = False

    fingerprint_91[base] = mags
    print(f"Base {base}: |A_d| = [{', '.join(f'{m:.3f}' for m in mags)}]")
    print(f"  Reflection symmetric magnitudes: {reflection_ok}")
    print(f"  Sum = {sum(A):.6f}")
    print()

# Now: compare with primes near 91
print(f"=== Comparison with primes ===\n")

primes_near = [83, 89, 97, 101]
for np in primes_near:
    chi_p = make_prime_chi(np, 5)  # same character index
    match_count = 0
    total_distance = 0

    for base in bases:
        if math.gcd(base, np) != 1:
            continue
        A = compute_Ad(np, base, chi_p)
        mags = tuple(round(abs(a), 6) for a in A)

        # Distance from n=91 fingerprint at this base
        if base in fingerprint_91 and len(mags) == len(fingerprint_91[base]):
            dist = sum((a - b_val)**2 for a, b_val in zip(mags, fingerprint_91[base]))**0.5
            total_distance += dist

    print(f"  p = {np}: total magnitude distance = {total_distance:.4f}")

# The key test: do the constraints at multiple bases
# leave room for a different factorization?
print(f"\n=== Constraint count ===\n")
for base in bases:
    b = base
    n_params = 2 * b  # complex A_d
    n_mag = b  # known magnitudes
    n_sum = 2  # sum = 0
    n_refl = b - 1  # reflection pairs (for odd b, middle is self-paired)
    n_constraints = n_mag + n_sum + n_refl
    n_free = n_params - n_constraints - 1  # -1 for global phase

    print(f"Base {b}: {n_params} params, {n_constraints} constraints, "
          f"{n_free} free phase DOF")

total_constraints = sum(
    b + 2 + b - 1 for b in bases
)
print(f"\nTotal constraints across {len(bases)} bases: {total_constraints}")
print(f"Unknown: 1 (the factorization)")
print(f"Overdetermination: {total_constraints - 1}")
