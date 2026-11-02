"""Exact local-factor references, independent of the production numerator formulas."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
from pathlib import Path
import subprocess


@lru_cache(None)
def reference_table(p):
    r, c = F(1, p), F(1, p - 1)
    numerator, mass, rv = F(), F(1), F(1)
    g0 = sum((r ** (2*j) for j in range(64)), F())
    g1 = sum((j*r ** (2*j) for j in range(64)), F())
    table = {}
    for v in range(241):
        if v:
            rv *= r
            numerator += (1-r)*rv*(v+c)
            mass += (1-r)*rv
        k = 1+r-rv/F(p+1)
        # Independent loss formula. Production instead adds its exact
        # geometric tail to the printed closed reset numerator.
        kn = k*c-rv*(F(v, p+1)+F(p*p+p+1, (p-1)*(p+1)**2))
        t, u, limit = numerator/mass, kn/k, 1+r
        result = dict(reset_factor=mass, reset_numerator=numerator, reset_average=t,
            alignment_factor=k, alignment_numerator=kn, alignment_average=u,
            alignment_tail=kn-numerator, limiting_factor=limit, limiting_average=c,
            reset_factor_relative_loss=(limit-mass)/limit, reset_average_loss=c-t,
            alignment_factor_relative_loss=(limit-k)/limit, alignment_average_loss=c-u,
            absent_factor=(1-r**3)/(1-r**2), absent_average=F(1, p*p-1))
        # A separate literal finite series and a geometric majorant check
        # the closed numerator, without using its production tail formula.
        partial = numerator+(1-r)*rv*r*r*((v+1+c)*g0+g1)
        residual = 2*(1-r)*r**(v+130)*(v+65+c)
        table[v] = (result, partial, residual)
    return table


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--driver', required=True)
    args = parser.parse_args()
    # Complete unit counts select primes independently of trial division.
    primes = [p for p in range(2, 241)
              if sum(gcd(a, p) == 1 for a in range(1, p)) == p-1]
    queries = [(p, v) for p in primes for v in range(241)]
    rejected = [(p, 1) for p in range(242) if p not in primes]+[(2, 241), (239, 999)]
    run = subprocess.run([str(Path(args.driver).absolute())],
        input=''.join(f'{p} {v}\n' for p, v in queries+rejected),
        text=True, capture_output=True, check=True, timeout=180)
    rows = run.stdout.splitlines()
    assert len(rows) == len(queries)+len(rejected)
    checks = 0

    def check(condition, detail):
        nonlocal checks
        checks += 1
        assert condition, detail

    for line, (p, v) in zip(rows, queries+rejected):
        parts = line.split()
        check(tuple(map(int, parts[:2])) == (p, v), ('metadata', p, v))
        valid = p in primes and v <= 240
        check(int(parts[2]) == valid, ('admission', p, v))
        if not valid:
            check(len(parts) == 3, ('rejected output', p, v))
            continue
        expected, partial, residual = reference_table(p)[v]
        check(len(parts) == len(expected)+3, ('fields', p, v))
        for token, (field, value) in zip(parts[3:], expected.items()):
            actual = F(token)
            check(actual == value, (p, v, field, actual, value))
            check(str(actual) == token, ('canonical spelling', p, v, field))
        check(partial <= expected['alignment_numerator'] <= partial+residual,
              ('independent finite series', p, v))
        c = F(1, p-1)
        check(0 <= expected['reset_average'] <= c and 0 <= expected['alignment_average'] <= c,
              ('actual local bounds', p, v))
        check(1 <= expected['reset_factor'] <= 1+F(1, p) and
              1 <= expected['alignment_factor'] <= 1+F(1, p), ('factor bounds', p, v))
        if not v:
            check(expected['reset_average'] == 0 and expected['reset_factor'] == 1 and
                  expected['alignment_factor'] == expected['absent_factor'] and
                  expected['alignment_average'] == expected['absent_average'], ('zero valuation', p))
    check(run.stderr.strip() == f'C_ASSERTIONS {120+len(queries)}', 'C assertions')
    print(f'PASS alignment local factors: {checks} exact reference checks; '
          f'{len(queries)} admitted prime/valuation pairs, {len(rejected)} rejected queries; '
          '120 C admission/preservation assertions plus successful metadata assertions. '
          'Independent finite sums, closed loss formula and geometric residual.')


if __name__ == '__main__':
    main()
