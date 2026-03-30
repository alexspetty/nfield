#!/usr/bin/env python3
"""
repetend_factor.py: Can the repetend of 1/n leak the factors of n?

The repetend of 1/n is the repeating block of the decimal expansion.
It's computable by long division without knowing the factors.
Its length is ord_b(n). Its digits ARE the orbit of the digit function.

For n = p*q, the repetend encodes both factors' periodicities.
The autocorrelation of the digit sequence should show peaks
at the factor periods. The collision count C(b^k) at the composite
is readable directly from the repetend autocorrelation at lag k.

Key idea: you don't need to scan all residues. You just need
the single sequence of digits of 1/n, and its self-correlation
structure tells you about the factors.
"""

import math
from collections import defaultdict

def repetend(n, base=10):
    """Compute the repeating block of 1/n in the given base.
    Returns the list of digits."""
    # Remove factors of base from n
    n0 = n
    for p in [2, 5]:
        while n0 % p == 0:
            n0 //= p
    if n0 == 1:
        return []  # terminating

    # Long division to find repeating part
    r = 1
    # Skip non-repeating prefix
    seen = {}
    digits = []
    for _ in range(n + 10):  # safety bound
        r = (r * base) % n0
        if r in seen:
            start = seen[r]
            return digits[start:]
        seen[r] = len(digits)
        d = (r * base) // n0
        digits.append(d)
        r = (r * base) % n0
        if r == 0:
            return digits

    return digits


def repetend_long_div(n, base=10):
    """Compute repeating digits of 1/n via long division.
    Returns (digits, period)."""
    # Remove base factors
    n0 = n
    prefix_len = 0
    for p in [2, 5]:
        while n0 % p == 0:
            n0 //= p
            prefix_len += 1

    if n0 == 1:
        return [], 0

    digits = []
    r = 1
    for _ in range(n0):
        r = (r * base) % n0
        d = (r * base) // n0
        digits.append(d)

    # The period is ord_base(n0)
    return digits, len(digits)


def digit_autocorrelation(digits, max_lag=None):
    """Compute autocorrelation: fraction of positions where
    digit[i] == digit[i+lag], for each lag."""
    L = len(digits)
    if max_lag is None:
        max_lag = L // 2
    max_lag = min(max_lag, L - 1)

    result = {}
    for lag in range(1, max_lag + 1):
        matches = 0
        for i in range(L):
            if digits[i] == digits[(i + lag) % L]:
                matches += 1
        result[lag] = matches / L
    return result


def digit_cross_correlation(digits, lag):
    """How many digit matches at this lag?"""
    L = len(digits)
    matches = 0
    for i in range(L):
        if digits[i] == digits[(i + lag) % L]:
            matches += 1
    return matches


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def mult_order(base, n):
    if gcd(base, n) != 1:
        return 0
    r = 1
    for k in range(1, n + 1):
        r = (r * base) % n
        if r == 1:
            return k
    return 0


def analyze_repetend(p, q, base=10):
    """Analyze the repetend of 1/(p*q) for factor signals."""
    n = p * q
    print(f"\n{'='*60}")
    print(f"  REPETEND ANALYSIS: 1/{n} = 1/({p} x {q})")
    print(f"{'='*60}")

    L_p = mult_order(base, p)
    L_q = mult_order(base, q)
    L_n = mult_order(base, n)
    print(f"\n  ord_{base}({p}) = {L_p}")
    print(f"  ord_{base}({q}) = {L_q}")
    print(f"  ord_{base}({n}) = {L_n}  (lcm = {math.lcm(L_p, L_q)})")

    # Get the repetend
    digits, period = repetend_long_div(n, base)
    print(f"  Repetend length: {period}")

    if period > 50000:
        print(f"  (too long for full analysis, sampling)")
        return

    if period <= 120:
        dstr = ''.join(str(d) for d in digits)
        print(f"  Digits: {dstr}")

    # Autocorrelation
    print(f"\n  AUTOCORRELATION (digit matches at lag k):")
    print(f"  Looking for peaks that reveal factor periods...")

    max_lag = min(period // 2, 500)
    autocorr = digit_autocorrelation(digits, max_lag)

    # Expected baseline: for random digits, P(match) = sum(freq_d^2)
    freq = defaultdict(int)
    for d in digits:
        freq[d] += 1
    baseline = sum((c / period) ** 2 for c in freq.values())
    print(f"  Baseline (random): {baseline:.4f}")

    # Find peaks above baseline
    peaks = []
    for lag, corr in sorted(autocorr.items()):
        if corr > baseline * 1.5:  # significant peak
            peaks.append((lag, corr))

    # Show top peaks
    peaks.sort(key=lambda x: -x[1])
    print(f"\n  Top autocorrelation peaks (>{baseline*1.5:.4f}):")
    for lag, corr in peaks[:20]:
        markers = []
        if L_p > 0 and lag % L_p == 0:
            markers.append(f"multiple of ord({p})={L_p}")
        if L_q > 0 and lag % L_q == 0:
            markers.append(f"multiple of ord({q})={L_q}")
        if lag == L_p:
            markers.append("FACTOR PERIOD")
        if lag == L_q:
            markers.append("FACTOR PERIOD")
        marker_str = f"  <- {', '.join(markers)}" if markers else ""
        print(f"    lag {lag:6d}: {corr:.4f}{marker_str}")

    # Key question: does lag = L_p or lag = L_q show a peak?
    print(f"\n  FACTOR PERIOD TEST:")
    if L_p <= max_lag:
        corr_p = autocorr.get(L_p, 0)
        print(f"    Autocorr at lag {L_p} (ord of {p}): {corr_p:.4f} "
              f"({'PEAK' if corr_p > baseline * 1.5 else 'no peak'}, "
              f"baseline={baseline:.4f})")
    if L_q <= max_lag:
        corr_q = autocorr.get(L_q, 0)
        print(f"    Autocorr at lag {L_q} (ord of {q}): {corr_q:.4f} "
              f"({'PEAK' if corr_q > baseline * 1.5 else 'no peak'}, "
              f"baseline={baseline:.4f})")

    # GCD test: if we find a peak at lag k, then gcd(b^k - 1, n)
    # might give a factor
    print(f"\n  GCD FACTOR EXTRACTION:")
    for lag, corr in peaks[:10]:
        bk = pow(base, lag, n)
        g = gcd(bk - 1, n)
        if 1 < g < n:
            print(f"    lag {lag}: gcd(10^{lag} - 1, {n}) = {g}  "
                  f"FACTOR FOUND! ({n} = {g} x {n//g})")
        else:
            print(f"    lag {lag}: gcd(10^{lag} - 1, {n}) = {g}  (trivial)")

    # Digit frequency analysis: does the digit distribution
    # reveal anything about the factors?
    print(f"\n  DIGIT FREQUENCY:")
    for d in range(base):
        f = freq.get(d, 0)
        print(f"    digit {d}: {f:5d} ({100*f/period:.1f}%)")

    # Spectral approach: DFT of digit sequence
    # Peaks in the DFT correspond to periodicities
    if period <= 10000:
        print(f"\n  FOURIER ANALYSIS of digit sequence:")
        import cmath
        N = period
        # Compute DFT at selected frequencies
        # We're looking for peaks at k = N/L_p and k = N/L_q
        target_freqs = set()
        if L_p > 0:
            target_freqs.add(N // L_p)
            for m in range(1, 6):
                target_freqs.add(m * N // L_p)
        if L_q > 0:
            target_freqs.add(N // L_q)
            for m in range(1, 6):
                target_freqs.add(m * N // L_q)
        # Also compute at some other frequencies for comparison
        other_freqs = set()
        for k in range(1, min(N // 2, 200)):
            other_freqs.add(k)

        all_freqs = sorted(target_freqs | other_freqs)
        all_freqs = [k for k in all_freqs if 0 < k < N // 2]

        dft_results = {}
        for k in all_freqs:
            s = sum(digits[j] * cmath.exp(-2j * cmath.pi * k * j / N)
                    for j in range(N))
            dft_results[k] = abs(s) / N

        # Find DFT peaks
        dft_peaks = sorted(dft_results.items(), key=lambda x: -x[1])

        print(f"  Top DFT peaks:")
        for k, mag in dft_peaks[:15]:
            implied_period = N / k if k > 0 else 0
            markers = []
            if L_p > 0 and abs(implied_period - L_p) < 0.5:
                markers.append(f"MATCHES ord({p})")
            if L_q > 0 and abs(implied_period - L_q) < 0.5:
                markers.append(f"MATCHES ord({q})")
            if L_p > 0 and abs(implied_period - L_p) / L_p < 0.01:
                markers.append(f"~ord({p})")
            if L_q > 0 and abs(implied_period - L_q) / L_q < 0.01:
                markers.append(f"~ord({q})")
            marker_str = f"  <- {', '.join(markers)}" if markers else ""
            print(f"    freq {k:6d}  |X|={mag:.4f}  "
                  f"(period={implied_period:.1f}){marker_str}")

        # Check if factor frequencies specifically
        print(f"\n  FACTOR FREQUENCY CHECK:")
        if L_p > 0 and N % L_p == 0:
            k_p = N // L_p
            mag_p = dft_results.get(k_p, 0)
            print(f"    freq {k_p} (period {L_p}, factor {p}): |X|={mag_p:.4f}")
        if L_q > 0 and N % L_q == 0:
            k_q = N // L_q
            mag_q = dft_results.get(k_q, 0)
            print(f"    freq {k_q} (period {L_q}, factor {q}): |X|={mag_q:.4f}")


def main():
    base = 10

    print("REPETEND FACTOR ANALYSIS")
    print("Can the digit sequence of 1/n reveal the factors of n?")

    test_cases = [
        (7, 11),      # 77
        (7, 13),      # 91
        (11, 13),     # 143
        (13, 17),     # 221
        (29, 31),     # 899
        (37, 41),     # 1517
        (101, 103),   # 10403
        (127, 131),   # 16637
    ]

    for p, q in test_cases:
        analyze_repetend(p, q, base)


if __name__ == '__main__':
    main()
