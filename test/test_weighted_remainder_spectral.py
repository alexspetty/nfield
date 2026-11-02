#!/usr/bin/env python3
"""Independent divisor inversion, primitive lattice counts and moment oracles.

Finite numerical comparisons are distinct from the Lean infinite-tail proofs.
No production computation is used to construct expected values.
"""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, prod
from pathlib import Path
import subprocess
from test_weighted_remainder_constants import log_reference, dec

getcontext().prec = 90
MEAN_KEYS = ("x h_sum h_mean correction_floor_sum correction_floor_mean "
    "correction_series_prefix product_lower product_upper "
    "nu_sum_lower nu_sum_upper nu_square_sum_lower nu_square_sum_upper "
    "nu_mean_lower nu_mean_upper nu_square_mean_lower nu_square_mean_upper "
    "first_prefix_lower first_prefix_upper first_tail_upper first_lower first_upper "
    "second_prefix_lower second_prefix_upper second_tail_upper second_lower second_upper "
    "nu_first_mean_bound nu_second_mean_bound").split()
checks = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


@lru_cache(None)
def divisors(n):
    return tuple(d for d in range(1, n+1) if n % d == 0)


@lru_cache(None)
def mobius(n):
    return 1 if n == 1 else -sum(mobius(d) for d in divisors(n) if d < n)


def isprime(n):
    return n > 1 and all(n % d for d in range(2, int(n**0.5)+1))


@lru_cache(None)
def h_reference(n):
    if n == 0:
        return F(0)
    # h=J2*rho^2/n^2. J2 counts literal primitive residue pairs;
    # phi counts units; Delta is a signed divisor sum, not a prime product.
    j2 = sum(gcd(gcd(a, b), n) == 1 for a in range(n) for b in range(n))
    phi = sum(gcd(a, n) == 1 for a in range(n))
    delta = sum((F(mobius(d), d**3) for d in divisors(n)), F(0))
    rho = F(phi, n)/delta
    return j2*rho*rho/n**2


@lru_cache(None)
def correction(n):
    if n == 0:
        return F(0)
    return h_reference(n)-sum((correction(d) for d in divisors(n) if d < n), F(0))


@lru_cache(None)
def product_reference(P):
    hi = prod((1+(h_reference(p)-1)/p for p in range(2, P+1) if isprime(p)), start=F(1))
    return max(F(0), hi-F(2, P)), hi


@lru_cache(None)
def profile_reference(p):
    if not isprime(p):
        return F(0), F(0)
    return tuple(x/(p-1) for x in log_reference(p))


@lru_cache(None)
def nu_reference(n):
    return tuple(sum((profile_reference(p)[i] for p in divisors(n) if isprime(p)), F(0))
                 for i in (0, 1))


@lru_cache(None)
def finite_mean_reference(N):
    hsum = sum((h_reference(n) for n in range(1, N+1)), F(0))
    signed = sum((correction(d)*(N//d) for d in range(1, N+1)), F(0))
    series = sum((correction(d)/d for d in range(1, N+1)), F(0))
    sums = tuple(sum((nu_reference(n)[i] for n in range(1, N+1)), F(0)) for i in (0, 1))
    squares = tuple(sum((nu_reference(n)[i]**2 for n in range(1, N+1)), F(0)) for i in (0, 1))
    return hsum, signed, series, sums, squares


@lru_cache(None)
def prime_reference(P):
    first = tuple(sum((profile_reference(p)[i]/p for p in range(2, P+1)), F(0)) for i in (0, 1))
    second = tuple(sum((profile_reference(p)[i]**2/p for p in range(2, P+1)), F(0)) for i in (0, 1))
    b = (2*P-1).bit_length()
    ft, st = F(2*(2*b+3), P), F(16, P)
    fl, fu, sl, su = first[0], first[1]+ft, second[0], second[1]+st
    return first[0], first[1], ft, fl, fu, second[0], second[1], st, sl, su, fu, fu*fu+su


def mean_reference(x, P):
    N = x.numerator//x.denominator
    hs, cs, series, nu, sq = finite_mean_reference(N)
    return dict(zip(MEAN_KEYS, [x, hs, hs/x, cs, cs/x, series, *product_reference(P),
        *nu, *sq, *(z/x for z in nu), *(z/x for z in sq), *prime_reference(P)]))


@lru_cache(None)
def decimal_nu_sums(N):
    primes = [p for p in range(2, N+1) if isprime(p)]
    profiles = {p: D(p).ln()/D(p-1) for p in primes}
    direct = [sum((profiles[p] for p in primes if n % p == 0), D(0)) for n in range(1, N+1)]
    first = sum(direct, D(0))
    second = sum((n*n for n in direct), D(0))
    # An independently ordered double-prime divisor count retains the diagonal.
    double = sum((profiles[p]*profiles[r]*D(N//(p*r//gcd(p, r))) for p in primes for r in primes), D(0))
    check(abs(second-double) < D('1e-80'), ('second prime-pair count', N))
    return first, second


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    ap.add_argument('--bin')
    args = ap.parse_args()
    queries = [(op, n) for op in ('F', 'A', 'P') for n in range(242)]
    cutoffs = (1, 2, 4, 17, 127, 240)
    means = [(F(n), P) for n in range(1, 241) for P in cutoffs]
    means += [(F(n)+offset, (n*11) % 240+1) for n in range(1, 241)
              for offset in (-F(1, 256), F(1, 256))]
    means += [(F(0), 1), (F(1, 2), 1), (F(1), 0), (F(1), 241),
              (F(2**254, 2**254-1), 239), (F(2**255, 2**255-1), 1)]
    lines_in = [f'{op} {n}' for op, n in queries] + [f'M {x} {P}' for x, P in means]
    run = subprocess.run([str(Path(args.driver).absolute())], input='\n'.join(lines_in)+'\n',
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = run.stdout.splitlines()
    check(lines and lines[0].startswith('EDGES '), lines[:1])
    edges = int(lines[0].split()[1])
    check(len(lines) == len(lines_in)+1, ('record count', len(lines)))
    for (op, n), line in zip(queries, lines[1:]):
        record = line.split()
        valid = (2 <= n <= 240 and isprime(n)) if op == 'F' else (0 <= n <= 240 if op == 'A' else 1 <= n <= 240)
        check(record[:2] == [op, str(int(valid))], ('scalar admission', op, n, record[:2]))
        if not valid:
            check(len(record) == 2, ('failure fields', op, n))
            continue
        expected = (h_reference(n), 1+(h_reference(n)-1)/n) if op == 'F' else (
            (h_reference(n), correction(n)) if op == 'A' else product_reference(n))
        check(tuple(map(F, record[2:])) == expected, ('independent scalar', op, n))
        for field in record[2:]:
            check(str(F(field)) == field, ('canonical endpoint', op, n, field))
        if op == 'F':
            check(0 < expected[0] <= expected[1] <= 1, ('positive factor', n))
            check(1-expected[0] <= F(2, n), ('local defect', n))
        if op == 'A' and n:
            check(h_reference(n) == sum((correction(d) for d in divisors(n)), F(0)), ('divisor inversion', n))
            check(correction(n) == 0 if mobius(n) == 0 else correction(n) != 0, ('squarefree correction', n))
    R = 4096
    ps = [p for p in range(2, R+1) if isprime(p)]
    first_long = sum((D(p).ln()/(D(p)*D(p-1)) for p in ps), D(0))
    second_long = sum((D(p).ln()**2/(D(p)*D(p-1)**2) for p in ps), D(0))
    product_long = prod((1+((1-D(1)/D(p)**2)*(D(p)**2/(D(p)**2+p+1))**2-1)/p for p in ps), start=D(1))
    valid_means = 0
    for (x, P), line in zip(means, lines[1+len(queries):]):
        record = line.split()
        valid = 1 <= x <= 240 and 1 <= P <= 240 and max(x.numerator.bit_length(), x.denominator.bit_length()) <= 255
        check(record[:2] == ['M', str(int(valid))], ('mean admission', x, P, record[:2]))
        if not valid:
            check(len(record) == 2, ('failed mean fields', x, P))
            continue
        valid_means += 1
        N = x.numerator//x.denominator
        check(list(map(int, record[2:5])) == [N, P, (2*P-1).bit_length()], ('metadata', x, P))
        check(len(record) == 33, ('mean field count', len(record)))
        actual = dict(zip(MEAN_KEYS, map(F, record[5:])))
        expected = mean_reference(x, P)
        for k in MEAN_KEYS:
            check(actual[k] == expected[k], ('exact mean endpoint', x, P, k, actual[k], expected[k]))
        for raw in record[5:]:
            check(str(F(raw)) == raw, ('canonical mean', x, P))
        check(actual['h_sum'] == actual['correction_floor_sum'], ('literal signed floor identity', x))
        check(actual['h_mean'] == actual['correction_floor_mean'], ('literal divisor denominator', x))
        first, second = decimal_nu_sums(N)
        for key, value in [('nu_sum', first), ('nu_square_sum', second),
                           ('nu_mean', first/dec(x)), ('nu_square_mean', second/dec(x))]:
            check(dec(actual[key+'_lower']) <= value <= dec(actual[key+'_upper']), ('decimal mean', x, P, key))
        check(first/dec(x) <= dec(actual['nu_first_mean_bound']), ('full first moment bound', x, P))
        check(second/dec(x) <= dec(actual['nu_second_mean_bound']), ('full second moment bound', x, P))
        check(dec(actual['first_lower']) <= first_long <= dec(actual['first_upper']), ('long finite prime first moment', x, P))
        check(dec(actual['second_lower']) <= second_long <= dec(actual['second_upper']), ('long finite prime second moment', x, P))
        check(dec(actual['product_lower']) <= product_long <= dec(actual['product_upper']), ('long finite prime product', x, P))
    cli_cases = 0
    if args.bin:
        binary = str(Path(args.bin).absolute())
        def invoke(words, expected=None):
            nonlocal cli_cases
            cli_cases += 1
            r = subprocess.run([binary, 'weighted-remainder-state', *words], text=True, capture_output=True)
            check((r.returncode == 0) == (expected is not None), ('CLI admission', words, r.returncode, r.stderr))
            if expected is not None:
                rows = [line.split('=', 1) for line in r.stdout.splitlines() if '=' in line and line.split('=', 1)[0].replace('_', '').isalpha()]
                actual = dict(rows)
                check(len(rows) == len(actual), ('duplicate CLI key', words))
                check(set(actual) == set(expected), ('CLI fields', words, set(actual)^set(expected)))
                for k, value in expected.items():
                    check(actual[k] == str(value), ('CLI endpoint', words, k))
                check('finite computations and infinite proofs are separate' in r.stdout, ('CLI boundary', words))
        for P in (1, 2, 7, 240):
            lo, hi = product_reference(P)
            invoke(['spectral-product', str(P)], {'prime_cutoff': P, 'product_lower': lo, 'product_upper': hi})
        for spelling, P in [('1', 1), ('5/2', 2), ('0005/0002', 7), ('240', 240), ('239999/1000', 127),
                            (str(F(2**254, 2**254-1)), 239)]:
            x = F(spelling)
            expected = mean_reference(x, P)
            expected.update(floor_x=x.numerator//x.denominator, prime_cutoff=P, prime_tail_binary_exponent=(2*P-1).bit_length())
            invoke(['spectral-mean', spelling, str(P)], expected)
        for words in [['spectral-product'], ['spectral-product', '1', 'extra'],
                      ['spectral-mean'], ['spectral-mean', '2'], ['spectral-mean', '2', '1', 'extra']]:
            invoke(words)
        for bad in ('0', '241', '-1', '+2', '2.0', '2/1', '9'*160):
            invoke(['spectral-product', bad])
        for bad in ('0', '1/2', '241', '240001/1000', '-1', '+2', '2.0', '1e1', '1/0', '1/-2',
                    '1//2', '/2', '1/', '', '1 2', '0'*160+'1', str(F(2**255, 2**255-1))):
            invoke(['spectral-mean', bad, '1'])
    print(f'PASS spectral arithmetic and moments: {checks} checks, {len(queries)+len(means)} API cases, '
          f'{edges} C edge checks, {valid_means} admitted rational means, {cli_cases} CLI cases; infinite proofs remain separate.')


if __name__ == '__main__':
    main()
