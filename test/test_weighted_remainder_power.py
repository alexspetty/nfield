#!/usr/bin/env python3
"""Independent rational and high-precision references for n^(-s)."""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path
import subprocess
from test_weighted_remainder_constants import log_reference

getcontext().prec = 100
GRID = 10**24
ERROR = F(25, 24*factorial(24))
checks = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def dec(x):
    x = F(x)
    return D(x.numerator)/D(x.denominator)


def down(x, grid=GRID):
    x *= grid
    return F(x.numerator//x.denominator, grid)


def up(x, grid=GRID):
    return -down(-x, grid)


@lru_cache(None)
def power_reference(n, s):
    if s.denominator == 1 or n == 1:
        value = F(1, n**int(s))
        return value, value
    ll, lh = log_reference(n)
    a, b = s*ll/128, s*lh/128
    assert 0 <= a <= b <= 1
    # Direct powers/factorials, independent of the C term recurrence.
    poly = lambda x: sum((x**k/factorial(k) for k in range(24)), F(0))
    lo = max(F(1), down(max(F(1), poly(a)-ERROR)))
    hi = up(poly(b)+ERROR)
    for _ in range(7):
        lo, hi = max(F(1), down(lo*lo)), up(hi*hi)
    return down(1/hi, 10**48), up(1/lo, 10**48)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    args = ap.parse_args()
    exponents = sorted(set([F(j, 2) for j in range(25)]+
                          [F(1, 1000), F(1, 3), F(10, 7), F(101, 100),
                           F(599, 100), F(37, 31), F(11999, 1000)]))
    queries = [(n, s) for s in exponents for n in range(1, 241)]
    huge = [F(1, 2**255), F(2**255-1, 2**252), F(2**248+1, 2**247)]
    queries += [(n, s) for s in huge for n in (1, 2, 8, 30, 239, 240)]
    queries += [(n, s) for n, s in [(0, F(3, 2)), (241, F(2)), (2, F(-1, 2)),
                (2, F(1201, 100)), (2, F(1, 2**256)), (2, F(2**256+1, 2**254))]]
    run = subprocess.run([str(Path(args.driver).absolute())],
                         input=''.join(f'{n} {s}\n' for n, s in queries),
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = run.stdout.splitlines()
    check(lines[0].startswith('EDGES '), lines[:1])
    edges = int(lines[0].split()[1])
    check(len(lines) == len(queries)+1, ('record count', len(lines)))
    values = {}
    exact_cases = 0
    for (n, s), line in zip(queries, lines[1:]):
        data = line.split()
        valid = (1 <= n <= 240 and 0 <= s <= 12 and
                 s.numerator.bit_length() <= 256 and s.denominator.bit_length() <= 256)
        check(data[:2] == ['P', str(int(valid))], ('admission', n, s, data[:2]))
        if not valid:
            check(len(data) == 2, ('failure record', n, s))
            continue
        check(len(data) == 4, ('field count', n, s))
        lo, hi = map(F, data[2:])
        check((lo, hi) == power_reference(n, s), ('direct power/grid endpoint', n, s))
        check(0 < lo <= hi <= 1, ('positive interval', n, s))
        value = (-dec(s)*D(n).ln()).exp()
        # Decimal is a numerical cross-check, never the source of a bound.
        tolerance = D('1e-95')
        check(dec(lo)-tolerance <= value <= dec(hi)+tolerance, ('independent exp/log', n, s))
        if s.denominator == 1:
            check(lo == hi == F(1, n**int(s)), ('exact integer exponent', n, s))
            exact_cases += 1
        elif s.denominator == 2:
            check(lo**2 <= F(1, n**s.numerator) <= hi**2, ('independent squared rational', n, s))
        check(hi-lo <= max(F(1), hi)*F(1, 10**19), ('bounded width', n, s))
        values[n, s] = lo, hi
    identities = 0
    for n in range(1, 241):
        for s in exponents:
            if (n, 2*s) in values:
                lo, hi = values[n, s]
                dl, dh = values[n, 2*s]
                check(lo*lo <= dh and dl <= hi*hi, ('doubling compatibility', n, s))
                identities += 1
    print(f'PASS: {checks} checks; {len(queries)} API records; {edges} C edge assertions; '
          f'{exact_cases} exact integer powers; {identities} exponent-doubling cases.')
    print('Independent Decimal exp/log, squared half-integer comparisons, direct rational '
          'polynomial endpoints and signed outward rounding. Universal containment is '
          'proved separately in Lean; numerical samples do not certify it.')


if __name__ == '__main__':
    main()
