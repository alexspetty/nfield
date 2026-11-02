#!/usr/bin/env python3
"""Full-period integer-lattice references, independent of the C law visitor.

Weights use Mobius inversion. Characteristic references use Decimal Taylor
series and an independently calculated Machin pi, not MPFR. Full-law bounds
are checked as bounds, without treating them as numerical samples of Y.
"""
import argparse
from collections import Counter
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import lcm
from pathlib import Path
import subprocess

getcontext().prec = 105
checks = 0


def check(ok, why):
    global checks
    checks += 1
    assert ok, why


@lru_cache(None)
def mu(n):
    return 1 if n == 1 else -sum(mu(d) for d in range(1, n) if n % d == 0)


@lru_cache(None)
def weight(k):
    return sum((F(mu(d), k*k*d)*sum((F(1, j) for j in range(1, k//d)), F())
                for d in range(1, k+1) if k % d == 0), F())


@lru_cache(None)
def law(M):
    weights = [weight(k)/3 for k in range(2, M+1)]
    denominator = lcm(*(w.denominator for w in weights))
    coefficients = [int(w*denominator) for w in weights]
    period = lcm(*range(1, M+1))
    values = [sum(c*(2*(a % k)-k+1) for k, c in enumerate(coefficients, 2)) for a in range(period)]
    counts = sorted(Counter(values).items())
    return values, counts, denominator


def mass(counts, denominator, lower=None, upper=None):
    return sum(n for y, n in counts if (lower is None or y >= lower*denominator)
               and (upper is None or y <= upper*denominator))


def max_window(counts, denominator, width):
    # Deliberately use an independent quadratic scan at small M; binary
    # search counts at large M avoids repeating the production sliding window.
    from bisect import bisect_right
    values = [v for v, _ in counts]
    prefix = [0]
    for _, n in counts:
        prefix.append(prefix[-1]+n)
    return max(prefix[bisect_right(values, value+width*denominator)]-prefix[i]
               for i, value in enumerate(values))


def dec(x):
    x = F(x)
    return D(x.numerator)/D(x.denominator)


def atan(n):
    return sum((D((-1)**k)/(D(2*k+1)*D(n)**(2*k+1)) for k in range(200)), D(0))


PI = 16*atan(5)-4*atan(239)


def cosine(x):
    x %= 2*PI
    if x > PI:
        x -= 2*PI
    term = result = D(1)
    for k in range(1, 160):
        term *= -x*x/D((2*k-1)*(2*k))
        result += term
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bin', required=True)
    binary = str(Path(parser.parse_args().bin).resolve())

    def run(*args, valid=True):
        p = subprocess.run([binary, 'weighted-remainder-state', *map(str, args)],
                           text=True, capture_output=True, timeout=60)
        check((p.returncode == 0) == valid, (args, p.stderr))
        if not valid:
            check(not p.stdout, ('partial invalid output', args))
            return {}
        check(not p.stderr, (args, p.stderr))
        result = {}
        for line in p.stdout.splitlines():
            key, sep, value = line.partition('=')
            if sep and key.replace('_', '').isalnum():
                result[key] = F(value)
                check(str(result[key]) == value, ('canonical fraction', key))
        return result

    for M in range(2, 13):
        values, counts, den = law(M)
        period = len(values)
        error = F(256*( (2*M-1).bit_length()+1 )**2, M)
        for degree in [0, 1, 2, 3, 4, 16]:
            r = run('law-moment', M, degree)
            check(r['period'] == period and r['distinct'] == len(counts), ('law size', M))
            check(r['finite'] == F(sum(v**degree for v in values), period*den**degree), ('moment', M, degree))
            check(r['absolute_moment'] == F(sum(abs(v)**degree for v in values), period*den**degree), ('absolute moment', M, degree))
            check(r['squared_l2_error'] == error, 'published cutoff budget')
        for x, margin in [(F(0), F(1, 7)), (F(values[0], den), F(100)), (F(2), F(1, 10))]:
            r = run('law-cdf', M, x, margin)
            check(r['finite'] == F(mass(counts, den, upper=x), period), ('CDF', M, x))
            lower = max(F(), F(mass(counts, den, upper=x-margin), period)-error/margin**2)
            upper = min(F(1), F(mass(counts, den, upper=x+margin), period)+error/margin**2)
            check((r['full_lower'], r['full_upper']) == (lower, upper), 'CDF full bounds')
        for lo, hi, margin in [(F(-1, 10), F(1, 5), F(1, 20)), (F(0), F(0), F(1)), (F(-200), F(200), F(100))]:
            r = run('law-window', M, lo, hi, margin)
            check(r['finite'] == F(mass(counts, den, lo, hi), period), ('window', M))
            check(r['finite_expanded'] == F(mass(counts, den, lo-margin, hi+margin), period), 'expanded window')
            check(0 <= r['full_lower'] <= r['full_upper'] <= 1, 'probability range')
        for width, margin in [(F(0), F(1, 10)), (F(1, 7), F(1, 30)), (F(3), F(100))]:
            r = run('law-concentration', M, width, margin)
            check(r['finite'] == F(max_window(counts, den, width), period), ('concentration', M))
            check(r['finite_expanded'] == F(max_window(counts, den, width+2*margin), period), 'expanded concentration')
        H = 53 if M in (2, 12) else 7
        lo, hi = F(-1, 9), F(2, 9)
        event = [lo*den <= v <= hi*den for v in values]
        r = run('law-recurrence', M, lo, hi, H)
        for h in range(H):
            exact = F(sum(event[n] and event[(n+h) % period] for n in range(period)), period)
            check(r[f'intersection_{h}'] == exact, ('recurrence', M, h))
        squares = sum(sum(event[(n+j) % period] for j in range(H))**2 for n in range(period))
        check(r['second_moment'] == F(squares, period*H*H), ('literal recurrence square', M))
        check(r['mean_square'] == F(sum(event), period)**2 <= r['second_moment'], 'recurrence inequality')
    for M, t in [(2, F()), (2, F(2**100, 3)), (3, F(-7, 5)), (5, F(1, 10000)),
                 (7, F(1, 3)), (8, F(-5)), (12, F())]:
        values, counts, den = law(M)
        exact = sum((cosine(dec(t*F(v, den)))*n for v, n in counts), D())/len(values)
        r = run('law-characteristic', M, t)
        check(dec(r['real_lower']) <= exact+D('1e-95') and exact-D('1e-95') <= dec(r['real_upper']), ('characteristic enclosure', M, t))
        check(r['imaginary'] == 0 and r['rounding_width'] == r['real_upper']-r['real_lower'], 'reflection and rounding')
        check(r['characteristic_error_upper']**2 >= t*t*r['squared_l2_error'], 'frequency cutoff budget')
        if not t:
            check(r['real_lower'] == r['real_upper'] == r['full_real_lower'] == r['full_real_upper'] == 1, 'zero frequency')
    for M in [2, 7, 12, 60, 240]:
        weights = [weight(k) for k in range(2, M+1)]
        retained = sum(weights, F())
        star = sum((w*(k-1)/3 for k, w in enumerate(weights, 2)), F())
        for n in [0, 1, M, M+1, -1, -2, -M-1, -M-2, 10**100, -10**100]:
            r = run('clock-difference', M, n)
            centered = sum((w*F(2*(n % k)-k+1, 3) for k, w in enumerate(weights, 2)), F())
            check(r['centered_clock'] == centered and r['stationary_age'] == star, ('integer clock', M, n))
            reflected = n if n >= 0 else -n-1
            check(r['completed_difference_available'] == (reflected <= M), 'completion flag')
            if reflected <= M:
                # Original unit-completed deficit: n minus capacity, evaluated
                # independently through the finite floor-sum energy identity.
                capacity = F(reflected, 3)+F(2, 3)*sum((k*weight(k)*(reflected//k) for k in range(2, reflected+1)), F())
                expected = (reflected-capacity)*(1 if n >= 0 else -1)
                check(r['completed_difference'] == expected, ('completed deficit', M, n))
                check(r['completed_difference'] == r['cutoff_difference']+r['tail_correction'], 'cutoff completion identity')
            else:
                check(r['completed_difference'] == r['tail_correction'] == 0, 'unavailable completion fields')
        for threshold, modulus in [(F(1, 100), 12), (F(1), 1), (F(100), 240)]:
            r = run('law-tail-bound', M, threshold, modulus)
            c = sum((w*(__import__('math').gcd(k, modulus)-1)/3 for k, w in enumerate(weights, 2)), F())
            lower = max(F(), c-threshold)**2/(modulus**2*r['full_variance_upper'])
            check(r['alignment_lower'] == c and r['tail_lower'] == lower, 'cylinder tail lower bound')
            check(0 <= r['tail_lower'] <= r['tail_upper'] <= F(1, 2), 'tail range')
    from math import gcd
    for P, length in [(4, 1), (12, 3), (60, 15), (240, 60)]:
        primes = [p for p in range(P//2+1, P+1) if sum(gcd(j, p) == 1 for j in range(1, p)) == p-1]
        minimum = min(sum((F(1, j*p) for j in range(1, p)), F()) for p in primes)
        r = run('law-activation', P, length, F(1, 1000))
        check(r['prime_count'] == len(primes), 'activation prime count')
        check(r['minimum_increment'] == minimum, 'activation increment')
        check(r['bias_sum'] == sum((F(length, p) for p in primes), F()), 'independent hit probabilities')
        check(r['squared_probability_upper'] == min(1, 400/(1+r['bias_sum'])), 'activation squared bound')
        run('law-activation', P, length, minimum, valid=False)
        run('law-activation', P, P//4+1, 0, valid=False)
    invalid = [('law-moment', 13, 2), ('law-moment', 2, 17), ('law-cdf', 3, 0, 0),
               ('law-window', 3, 2, 1, 1), ('law-concentration', 3, -1, 1),
               ('law-characteristic', 3, '1/0'), ('law-characteristic', 3, '1/2/3'),
               ('law-recurrence', 3, 0, 1, 0), ('law-recurrence', 3, 0, 1, 241),
               ('law-tail-bound', 3, 0, 12), ('clock-difference', 241, 0),
               ('clock-difference', 2, '+1'), ('clock-difference', 2, '1.5'),
               ('law-moment', 2, 2, 'extra'), ('law-characteristic', 2, 2**256)]
    for args in invalid:
        run(*args, valid=False)
    print(f'PASS finite laws and cutoff differences: {checks} checks; complete periods through M=12, literal recurrence squares, Decimal characteristic functions, signed completion and invalid inputs.')


if __name__ == '__main__':
    main()
