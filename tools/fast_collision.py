#!/usr/bin/env python3
"""
fast_collision.py: Fast collision count computation.

Three approaches compared:
1. Brute force: O(n) per multiplier
2. Bin intersection: O(b) per multiplier (if it works)
3. FFT: O(n log n) for all multipliers

The bin intersection approach: C(g) = sum_d |B_d ∩ g^{-1}B_d|.
Each bin B_d = {r : floor(br/n) = d} is an interval [lo_d, hi_d].
g^{-1}B_d = {r : floor(b*g*r/n) = d} is also an interval.
The intersection is two overlapping intervals mod n.
"""

import math
import time
from collections import defaultdict

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def modinv(a, m):
    """Extended Euclidean algorithm for modular inverse."""
    if gcd(a, m) != 1:
        return None
    g, x, _ = extended_gcd(a, m)
    return x % m

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

# Method 1: Brute force O(n)
def collision_brute(n, g, base=10):
    count = 0
    for r in range(1, n):
        gr = (g * r) % n
        if gr == 0:
            continue
        if (base * r) // n == (base * gr) // n:
            count += 1
    return count

# Method 2: Bin intersection O(b)
def collision_bins(n, g, base=10):
    """Compute C(g) via bin interval intersections.

    Bin d = {r in 1..n-1 : floor(b*r/n) = d}
          = {r : d*n/b <= r < (d+1)*n/b}
          = {r : ceil(d*n/b) <= r <= floor(((d+1)*n - 1)/b)}

    We want: for each d, count r in B_d such that g*r mod n is also in B_d.

    g*B_d mod n = {g*r mod n : r in B_d} is NOT an interval in general.
    But g^{-1}*B_d = {r : g*r mod n in B_d} IS a union of intervals
    (in fact it's a single interval mod n if gcd(g,n)=1).

    Actually, {r : g*r mod n in [a, b]} = {r : r in [g^{-1}*a, g^{-1}*b] mod n}
    which is a single interval mod n.

    So C_d(g) = |[lo_d, hi_d] ∩ [g^{-1}*lo_d, g^{-1}*hi_d] mod n|

    Wait, that's not right either. We need r such that BOTH:
      floor(b*r/n) = d       (r in bin d)
      floor(b*gr/n) = d      (gr mod n in bin d)

    The second condition: gr mod n in [lo_d, hi_d].
    So r in g^{-1} * [lo_d, hi_d] mod n.

    If g_inv = g^{-1} mod n, then r must be in:
      [g_inv * lo_d mod n, g_inv * hi_d mod n] (modular interval)

    AND r must be in [lo_d, hi_d] (regular interval).

    The intersection of a regular interval with a modular interval
    can be computed in O(1).
    """
    if gcd(g, n) != 1:
        return 0

    g_inv = modinv(g, n)
    if g_inv is None:
        return 0

    total = 0
    for d in range(base):
        # Bin d boundaries
        lo = math.ceil(d * n / base)
        hi = ((d + 1) * n - 1) // base
        if lo > hi or lo >= n or hi < 1:
            continue
        lo = max(lo, 1)
        hi = min(hi, n - 1)
        bin_size = hi - lo + 1

        # Where does g^{-1} map this bin?
        # r must satisfy: g*r mod n in [lo, hi]
        # i.e., r in {g_inv * s mod n : s in [lo, hi]}
        # This is the interval [g_inv * lo mod n, g_inv * hi mod n] mod n
        # but as a modular arithmetic set

        # For each r in [lo, hi], check if g*r mod n is in [lo, hi]
        # This is still O(bin_size) per bin = O(n/b) total = O(n/b)
        # Not O(b)! Need a smarter approach.

        # Smarter: count integers r in [lo, hi] such that
        # (g*r mod n) is in [lo, hi].
        #
        # g*r mod n in [lo, hi] means:
        # there exists k such that lo <= g*r - k*n <= hi
        # i.e., (lo + k*n)/g <= r <= (hi + k*n)/g
        #
        # For r in [lo, hi], k ranges over a few values.
        # g*lo <= g*r <= g*hi, so k ranges from
        # floor(g*lo/n) to floor(g*hi/n), which is at most g values.
        # But g can be large...

        # Alternative: use the formula for counting lattice points
        # in the intersection of two Beatty-like intervals.
        #
        # Actually for the fast method we need to count:
        # |{r in [lo, hi] : (g*r) mod n in [lo, hi]}|
        #
        # = |{r in [lo, hi] : frac(g*r/n) in [lo/n, (hi+1)/n)}|
        #
        # This is a problem about the distribution of {g*r/n} for
        # r in an interval. By the three-distance theorem or
        # Weyl-type bounds, this can be estimated, but exact count
        # requires more work.
        #
        # For now, let's use the direct counting but note the
        # theoretical path.

        for r in range(lo, hi + 1):
            gr = (g * r) % n
            if gr == 0:
                continue
            if lo <= gr <= hi:
                total += 1

    return total


# Method 3: FFT for all C(g) at once
def collision_all_fft(n, base=10):
    """Compute C(g) for all g using FFT-like approach.

    d(r) = floor(b*r/n) for r in 1..n-1.
    C(g) = #{r : d(r) == d(g*r mod n)}.

    This is the multiplicative autocorrelation of d.
    We can compute it via additive convolution on (Z/nZ)*.

    For each digit value v, define indicator I_v(r) = 1 if d(r)=v.
    Then C(g) = sum_v sum_r I_v(r) * I_v(g*r mod n)
             = sum_v (I_v * I_v)(g)  [multiplicative convolution]

    Via DFT on (Z/nZ)*, this becomes:
    C_hat(chi) = sum_v |I_v_hat(chi)|^2

    Then C(g) = (1/phi(n)) sum_chi C_hat(chi) * chi(g)

    But computing DFT on (Z/nZ)* is O(phi(n)^2) naively.
    With number-theoretic transform tricks, maybe O(n log n).

    For now, let's use the direct brute approach for all g
    but with the digit array precomputed.
    """
    # Precompute digit function
    digit = [0] * n
    for r in range(1, n):
        digit[r] = (base * r) // n

    # Compute C(g) for all g coprime to n
    cg = {}
    for g in range(1, n):
        if gcd(g, n) != 1:
            continue
        count = 0
        for r in range(1, n):
            gr = (g * r) % n
            if gr == 0:
                continue
            if digit[r] == digit[gr]:
                count += 1
        cg[g] = count
    return cg


# Method 4: Precompute digit array, O(n) per g but fast constant
def collision_fast_brute(n, g, digit_array, base=10):
    """O(n) but with precomputed digit array (no division in loop)."""
    count = 0
    for r in range(1, n):
        gr = (g * r) % n
        if gr == 0:
            continue
        if digit_array[r] == digit_array[gr]:
            count += 1
    return count


def test_bin_method():
    """Verify bin method gives same results as brute force."""
    print("VERIFYING BIN INTERSECTION METHOD")
    print()

    base = 10
    test_ns = [77, 91, 143, 221, 899]
    for n in test_ns:
        if gcd(n, base) != 1:
            continue
        print(f"  n={n}:", end=" ")
        errors = 0
        tested = 0
        for g in range(2, min(n, 50)):
            if gcd(g, n) != 1:
                continue
            cb = collision_brute(n, g, base)
            ci = collision_bins(n, g, base)
            if cb != ci:
                errors += 1
                if errors <= 3:
                    print(f"MISMATCH g={g}: brute={cb}, bins={ci}")
            tested += 1
        if errors == 0:
            print(f"OK ({tested} multipliers tested)")
        else:
            print(f"{errors} errors out of {tested}")


def benchmark():
    """Compare speeds."""
    print("\nBENCHMARK: time to compute C(g) for one multiplier")
    print()

    base = 10
    sizes = [77, 221, 899, 3007, 10403]

    for n in sizes:
        if gcd(n, base) != 1:
            continue
        g = 2
        while gcd(g, n) != 1:
            g += 1

        # Brute force
        t0 = time.time()
        for _ in range(max(1, 10000 // n)):
            cb = collision_brute(n, g, base)
        t1 = time.time()
        brute_time = (t1 - t0) / max(1, 10000 // n)

        # Bin method
        t0 = time.time()
        for _ in range(max(1, 10000 // n)):
            ci = collision_bins(n, g, base)
        t1 = time.time()
        bin_time = (t1 - t0) / max(1, 10000 // n)

        print(f"  n={n:6d}: brute={brute_time*1e6:8.1f}us  "
              f"bins={bin_time*1e6:8.1f}us  "
              f"ratio={brute_time/bin_time if bin_time > 0 else 0:.2f}x  "
              f"C({g})={cb}")


def explore_deranging_structure():
    """The real question: can we find deranging multipliers fast?

    Key insight from the composite gate test:
    g is deranging at pq iff g mod p is deranging at p AND
    g mod q is deranging at q.

    So if we KNEW the factors, we could compute the deranging set
    in O(b * (p + q)) = O(b * sqrt(n)).

    But we don't know the factors. However:
    - The deranging set at any prime p has exactly b-1 elements.
    - These elements are determined by p mod b^2 (finite determination).
    - For a semiprime n=pq, the deranging set has size related to
      the factor deranging sets.

    Can we extract structural information from the deranging set
    of the composite WITHOUT knowing the factors?
    """
    print("\nDERANGING STRUCTURE ANALYSIS")
    print()

    base = 10
    semiprimes = [(7, 11), (11, 13), (13, 17), (29, 31), (37, 41)]

    for p, q in semiprimes:
        n = p * q

        # Find deranging set at composite
        ds = []
        for g in range(2, n):
            if gcd(g, n) != 1:
                continue
            if collision_brute(n, g, base) == 0:
                ds.append(g)

        print(f"  n={n} = {p}x{q}:")
        print(f"    Deranging set: {ds}")
        print(f"    Count: {len(ds)}")

        # The deranging elements satisfy:
        # g mod p in deranging(p) AND g mod q in deranging(q)
        # So the deranging set is the CRT lift of
        # deranging(p) x deranging(q).
        #
        # Size = |deranging(p)| * |deranging(q)| (by CRT)
        #      = d_p * d_q
        #
        # For primes where d_p = b-1 = 9 (i.e., all non-identity
        # elements are deranging), d_p * d_q = 81.
        # But we see 9 deranging at the composite, not 81.
        #
        # That's because the CRT lifts can collide with non-coprime
        # elements. Actually no, all lifted elements are coprime to n.
        #
        # Wait, I need to recount. At p=13, deranging = 9 elements
        # out of 12. At q=17, deranging = 9 out of 16.
        # CRT gives 9*9 = 81 pairs, each lifting to a unique
        # residue mod 221. But phi(221) = 192. So 81 out of 192
        # should be deranging. But we see only 9.
        #
        # Something is wrong with my understanding. Let me recheck.

        # Let me verify the "both deranging" claim more carefully
        ds_p = []
        for g in range(2, p):
            if collision_brute(p, g, base) == 0:
                ds_p.append(g)

        ds_q = []
        for g in range(2, q):
            if collision_brute(q, g, base) == 0:
                ds_q.append(g)

        print(f"    Deranging at {p}: {ds_p} (count {len(ds_p)})")
        print(f"    Deranging at {q}: {ds_q} (count {len(ds_q)})")

        # CRT lift of all pairs
        crt_lifts = []
        for gp in ds_p:
            for gq in ds_q:
                # Find g such that g = gp mod p and g = gq mod q
                # g = gp * q * modinv(q, p) + gq * p * modinv(p, q) mod n
                g_lift = (gp * q * modinv(q, p) + gq * p * modinv(p, q)) % n
                crt_lifts.append(g_lift)

        crt_lifts_set = set(crt_lifts)
        ds_set = set(ds)

        print(f"    CRT lifts of deranging(p) x deranging(q): "
              f"{len(crt_lifts_set)} elements")
        print(f"    Actual deranging at {n}: {len(ds_set)} elements")
        print(f"    Deranging subset of CRT lifts: "
              f"{ds_set.issubset(crt_lifts_set)}")
        print(f"    CRT lifts subset of deranging: "
              f"{crt_lifts_set.issubset(ds_set)}")

        # So the CRT lifts are a SUPERSET of the actual deranging set.
        # The actual deranging set is smaller. Why?
        # Because being deranging at BOTH factors is necessary but
        # not sufficient for being deranging at the composite!

        # Check: which CRT lifts are NOT deranging at composite?
        false_deranging = crt_lifts_set - ds_set
        if false_deranging:
            print(f"    CRT lifts that are NOT deranging at {n}: "
                  f"{len(false_deranging)}")
            for g in sorted(list(false_deranging))[:5]:
                cn = collision_brute(n, g, base)
                print(f"      g={g}: C_n(g)={cn}, "
                      f"g mod {p}={g%p} (deranging at {p}: {g%p in ds_p}), "
                      f"g mod {q}={g%q} (deranging at {q}: {g%q in ds_q})")
        print()


if __name__ == '__main__':
    test_bin_method()
    benchmark()
    explore_deranging_structure()
