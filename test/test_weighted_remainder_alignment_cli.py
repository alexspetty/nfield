#!/usr/bin/env python3
"""Independent growth readouts, defining sums and CLI admission checks.

Decimal transcendental values are numerical references, not certificates.
The production intervals use rational remainder bounds. No asymptotic is tested.
"""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm, prod, isqrt
from pathlib import Path
import subprocess

getcontext().prec = 70
GAMMA = D('0.5772156649015328606065120900824024310421593359399235988057672348849')
ZETA2 = D('1.64493406684822643647241516664602518921894990120679843773555822937')
PRIMES = [p for p in range(2, 241) if sum(gcd(a, p) == 1 for a in range(1, p)) == p-1]
checks = 0


def check(ok, detail):
    global checks
    checks += 1
    assert ok, detail


def dec(x):
    x = F(x)
    return D(x.numerator)/D(x.denominator)


@lru_cache(None)
def weight(k):
    # Direct reduced reciprocal sum, unlike the Euler growth implementation.
    return sum((F(1, a*k*k) for a in range(1, k) if gcd(a, k) == 1), F())


def run(binary, *args, valid=True):
    result = subprocess.run([binary, 'weighted-remainder-state', *map(str, args)],
                            capture_output=True, text=True, timeout=30)
    check((result.returncode == 0) == valid, (args, result.stderr))
    if not valid:
        check(not result.stdout.strip(), ('no partial result', args))
        return {}
    check(not result.stderr, (args, result.stderr))
    rows = {}
    for line in result.stdout.splitlines():
        if '=' in line and line.split('=', 1)[0].replace('_', '').isalnum():
            key, value = line.split('=', 1)
            rows[key] = F(value)
            check(str(rows[key]) == value, ('canonical', key, args))
    return rows


def encloses(row, key, value):
    low, high = dec(row[key+'_lower']), dec(row[key+'_upper'])
    check(low <= value+D('1e-60') and value-D('1e-60') <= high,
          ('enclosure', key, low, value, high))


def growth(binary, n, m, M, N, P, lcm_mode=False):
    row = run(binary, *(['alignment-lcm', m, M, N, P] if lcm_mode else
                        ['alignment-growth', n, m, M, N, P]))
    check(row['modulus'] == n and row['lcm'] == lcm(*range(1, m+1)), 'LCM metadata')
    check(row['lcm_match'] == (n == row['lcm']), 'LCM equality')
    check(row['normalized_available'] == (n >= 3), 'normalization flag')
    check(row['lcm_bounds_available'] == (n == row['lcm'] and m >= 4), 'loss flag')
    primes = [p for p in PRIMES if n % p == 0]
    check(row['tower_prime'] == (primes[0] if len(primes) == 1 else 0), 'tower flag')
    check(row['sqrt_floor'] == isqrt(m), 'sqrt floor')
    inverse = prod((F(p, p-1) for p in PRIMES if p <= m), start=F(1))
    plus = prod((F(p+1, p) for p in PRIMES if p <= m), start=F(1))
    check(row['mertens_inverse_product'] == inverse, 'Mertens inverse product')
    check(row['mertens_plus_product'] == plus, 'Mertens plus product')
    encloses(row, 'mertens_prime_log', sum((D(p).ln()/p for p in PRIMES if p <= m), D(0)))
    encloses(row, 'limiting_prime_log', sum((D(p).ln()/(p-1) for p in PRIMES if p <= m), D(0)))
    kappa = GAMMA.exp()/ZETA2
    encloses(row, 'exp_gamma', GAMMA.exp())
    encloses(row, 'kappa', kappa)
    encloses(row, 'Gamma', kappa/3)
    encloses(row, 'reset_leading', kappa*D(m).ln()**2)
    encloses(row, 'alignment_leading', kappa*D(m).ln()**2/3)
    if n >= 3:
        norm = D(n).ln().ln()**2
        encloses(row, 'normalizer', norm)
        if n <= 240:
            reset = sum((F(gcd(a, n)**2, a*n) for a in range(1, n+1)), F())-1
            encloses(row, 'normalized_reset', dec(reset)/norm)
        for key, numer in [('normalized_reset', 'reset'), ('normalized_alignment', 'alignment')]:
            check(row[key+'_lower'] <= row[key+'_upper'], ('interval order', key))
            # Bounds must contain the source interval divided by the actual normalizer.
            check(dec(row[key+'_lower']) <= dec(row[numer+'_lower'])/norm+D('1e-60'), key)
            check(dec(row[key+'_upper']) >= dec(row[numer+'_upper'])/norm-D('1e-60'), key)
    else:
        check(row['normalizer_lower'] == row['normalizer_upper'] == 0, 'unavailable normalizer')
    if row['lcm_bounds_available']:
        check(row['reset_factor_loss_sum'] <= row['lcm_factor_loss_upper'], 'reset LCM factor loss')
        check(row['alignment_factor_loss_sum'] <= row['lcm_factor_loss_upper'], 'alignment LCM factor loss')
        check(row['reset_log_loss_upper'] <= row['lcm_log_loss_upper'], 'reset LCM log loss')
        check(row['alignment_log_loss_upper'] <= row['lcm_log_loss_upper'], 'alignment LCM log loss')
    else:
        check(row['lcm_factor_loss_upper'] == row['lcm_log_loss_upper'] == 0, 'unavailable losses')
    if row['tower_prime']:
        check(row['reset_prefix'] <= row['tower_reset_upper'], 'tower reset bound')
        check(row['alignment_prefix'] <= row['tower_alignment_upper'], 'tower alignment bound')
        check(row['tower_combined_upper'] == row['tower_reset_upper']+row['tower_alignment_upper'], 'combined tower')
    else:
        check(row['tower_combined_upper'] == 0, 'unavailable tower')
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bin', required=True)
    binary = str(Path(parser.parse_args().bin).resolve())
    for m in [1, 2, 3, 4, 5, 7, 12, 24, 60, 120, 240]:
        growth(binary, lcm(*range(1, m+1)), m, max(2, min(m, 60)), 12, 17, True)
    for n, m, M, N, P in [(1, 2, 2, 1, 1), (2, 240, 240, 240, 240),
                          (3, 3, 12, 1, 1), (12, 5, 12, 24, 24),
                          (2**240, 16, 60, 24, 30), (239**240, 239, 2, 1, 1),
                          (2**100*3**100, 30, 24, 12, 7)]:
        growth(binary, n, m, M, N, P)
    for n in [1, 2, 12, 60, 239, 240]:
        row = run(binary, 'alignment', n, 240, 12, 12)
        reset = sum((F(gcd(a, n)**2, a*n) for a in range(1, n+1)), F())-1
        check(row['exact_reset'] == row['reset_lower'] == row['reset_upper'] == reset, 'triangular reset')
        check(row['alignment_prefix'] == sum((weight(k)*(gcd(k, n)-1)/3 for k in range(2, 241)), F()), 'alignment defining sum')
    for p, v in [(2, 0), (2, 240), (3, 4), (239, 1)]:
        row = run(binary, 'alignment-local', p, v)
        factor = 1+sum((F(p-1, p**(j+1)) for j in range(1, v+1)), F())
        numerator = sum((F(p-1, p**(j+1))*(j+F(1, p-1)) for j in range(1, v+1)), F())
        check(row['reset_factor'] == factor and row['reset_numerator'] == numerator, 'local defining sums')
    for k in [2, 6, 239, 240]:
        row = run(binary, 'harmonic-local', k, 24)
        check(row['coefficient'] == k*weight(k), 'local harmonic coefficient')
        check(row['mobius_sum'] == 0, 'linear cancellation')
    invalid = [('alignment', n, 12, 12, 12) for n in ['0', '-1', '+12', '12/1', '241', str(2**241), '1x', '1'*1235]]
    invalid += [('alignment-local', 4, 1), ('alignment-local', 2, 241),
                ('alignment-lcm', 0, 12, 12, 12), ('alignment-lcm', 241, 12, 12, 12),
                ('alignment-growth', 12, 4, 1, 12, 12), ('harmonic-local', 1, 12),
                ('alignment', 12, 12, 0, 12), ('alignment', 12, 12, 12, 241),
                ('alignment', 12, 12, 12, 12, 'extra')]
    for args in invalid:
        run(binary, *args, valid=False)
    help_text = subprocess.check_output([binary, 'help', 'weighted-remainder-state'], text=True)
    for action in ['alignment', 'alignment-local', 'harmonic-local', 'alignment-lcm', 'alignment-growth']:
        check('weighted-remainder-state '+action+' ' in help_text, ('help', action))
    print(f'PASS alignment CLI and growth: {checks} checks; defining sums, independent Decimal references, LCM losses, towers and rejected inputs.')


if __name__ == '__main__':
    main()
