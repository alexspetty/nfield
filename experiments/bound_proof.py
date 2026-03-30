#!/usr/bin/env python3
"""
Tighten the bound on |G(k)| and |coupling|.

G(k) = sum_{l=0}^{b-1} floor(lk/b) * psi(l)

where psi(l) = omega^l, omega = primitive b-th root.

Abel summation: G(k) = sum_{l=0}^{b-2} [floor(lk/b) - floor((l+1)k/b)] S(l)
                      + floor((b-1)k/b) S(b-1)

where S(L) = sum_{l=0}^{L} psi(l) = (omega^{L+1} - 1)/(omega - 1).

floor((l+1)k/b) - floor(lk/b) = d_l is 1 when lk crosses a
multiple of b, and 0 otherwise. There are exactly k-1 such
crossings for l = 0,...,b-1.

Actually, let me use the REVERSE Abel summation:
G(k) = floor((b-1)k/b) * S(b-1) - sum_{l=0}^{b-2} S(l) * [floor((l+1)k/b) - floor(lk/b)]
     = (k-1) * S(b-1) - sum_{crossings} S(l_j)

where l_j are the positions where floor((l+1)k/b) > floor(lk/b),
i.e., where (l+1)k/b crosses an integer.

The crossings occur at l = ceil(jb/k) - 1 for j = 1,...,k-1.

S(b-1) = sum_{l=0}^{b-1} psi(l) = (omega^b - 1)/(omega - 1) = 0
(complete character sum).

So G(k) = 0 - sum_{crossings} S(l_j) = -sum_{j=1}^{k-1} S(l_j)

where l_j = ceil(jb/k) - 1 = the last l before the j-th crossing.

This is clean! G(k) is minus the sum of partial character sums
at the crossing points of the Beatty staircase.
"""
import cmath, math

def test_abel(b, r):
    """Verify G(k) = -sum S(l_j) for fine character psi of order r."""
    omega = cmath.exp(2j * cmath.pi * r / b)

    # Partial sums S(L) = sum_{l=0}^{L} omega^l
    def S(L):
        if L < 0:
            return 0
        return sum(omega**l for l in range(L+1))

    print(f"\nBase {b}, fine character r={r}:")
    print(f"|1/(omega-1)| = {1/abs(omega-1):.4f}")
    print(f"Bound on |S(L)| <= 2/|omega-1| = {2/abs(omega-1):.4f}")

    for k in range(1, min(b, 8)):
        # Direct G(k)
        G_direct = sum((l*k//b) * omega**l for l in range(b))

        # Via Abel: G(k) = -sum S(l_j) at crossings
        crossings = []
        for j in range(1, k):
            # Crossing at l where floor((l+1)k/b) > floor(lk/b)
            # i.e., l+1 >= jb/k, l < jb/k
            # l_j = ceil(jb/k) - 1
            l_j = math.ceil(j * b / k) - 1
            crossings.append(l_j)

        G_abel = -sum(S(l_j) for l_j in crossings)

        err = abs(G_direct - G_abel)

        # Bound: |G(k)| <= (k-1) * 2/|omega-1|
        bound = (k-1) * 2 / abs(omega - 1)

        print(f"  k={k}: |G|={abs(G_direct):.4f}, Abel={abs(G_abel):.4f}, "
              f"err={err:.2e}, bound={bound:.4f}, "
              f"ratio={abs(G_direct)/bound:.4f}" if bound > 0 else "")

# Test at several bases
for b in [5, 7, 13, 31]:
    test_abel(b, 1)  # r=1: fine character of maximal order

# Now: the coupling = sum_{k=2}^{b-1} chi_bar(k) * G(k)
# = -sum_{k=2}^{b-1} chi_bar(k) * sum_{j=1}^{k-1} S(l_j(k))
# = -sum over all (k, j) pairs of chi_bar(k) * S(l_j(k))
#
# The total number of (k,j) pairs: sum_{k=2}^{b-1} (k-1) = (b-1)(b-2)/2.
#
# Each S(l_j) is bounded by 2/|omega-1| ~ b/(pi*r).
# Each chi_bar(k) has magnitude 1.
#
# WORST CASE: |coupling| <= (b-1)(b-2)/2 * b/(pi*r)
#
# But the chi_bar(k) values oscillate, so we expect cancellation.
# The question: how much cancellation?
#
# The coupling is a double sum over k and j. For fixed j,
# the sum over k involves chi_bar(k) weighted by S(l_j(k)).
# l_j(k) = ceil(jb/k) - 1 depends on k through the Beatty
# structure. As k varies, l_j moves, and S(l_j) changes.
#
# For LARGE j (close to k), l_j is close to b-1 and S(l_j)
# is close to S(b-1) = 0. So the large-j terms contribute
# little. The main contribution comes from small j.
#
# For j = 1: l_1(k) = ceil(b/k) - 1. As k goes from 2 to b-1:
# l_1 decreases from b/2 to 1. The partial sums S(l_1)
# at these points oscillate.

print("\n\n=== Coupling analysis for base 13, r=1 ===")
b = 13
omega = cmath.exp(2j * cmath.pi / b)

def S(L):
    return sum(omega**l for l in range(L+1)) if L >= 0 else 0

# Compute coupling contribution from each j
print(f"\nContribution by j (summed over k):")
total_coupling = 0
for j in range(1, b-1):
    contrib = 0
    for k in range(j+1, b):  # k > j for the crossing to exist
        l_j = math.ceil(j * b / k) - 1
        contrib += S(l_j)  # chi_bar(k) is not included here
    print(f"  j={j}: |contrib| = {abs(contrib):.4f}")
    total_coupling += abs(contrib)

print(f"\nTotal |coupling| bound (triangle ineq): {total_coupling:.4f}")
print(f"|F0| * |Q_bound| ~ b^2/pi = {b*b/math.pi:.4f}")
print(f"Ratio ~ {total_coupling / (b*b/math.pi):.4f}")
print(f"log(b) = {math.log(b):.4f}")
