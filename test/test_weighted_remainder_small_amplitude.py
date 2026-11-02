#!/usr/bin/env python3
"""Literal small-conductor series and the induced modulus-six factor."""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from pathlib import Path
import subprocess
from test_weighted_remainder_character import cotangent, product, progressions, PI, PI_LO, PI_HI
from test_weighted_remainder_cotangent import zeta_three
from test_weighted_remainder_fourier import dec

getcontext().prec = 90
checks = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def prefix(q, N):
    # Residue progressions, independently ordered from the C n-loop.
    return sum((F(1, n*n) for n in range(1, N+1, q)), F(0))-sum(
        (F(1, n*n) for n in range(q-1, N+1, q)), F(0))


def full(q):
    return (progressions(F(1, q))[1]-progressions(F(q-1, q))[1])/(q*q)


def half_minus(a, b):
    l, u = product(a, b)
    return F(1, 2)-u, F(1, 2)-l


def reference(N, K):
    p, c, s = prefix(3, N), prefix(4, N), prefix(6, N)
    tail = F(1, N);three = p-tail, p+tail;catalan = c-tail, c+tail;six = s-tail, s+tail
    z = sum((F(1, n**3) for n in range(1, K+1)), F(0));zh = z+F(1, 2*K*K)
    sl, su = cotangent(F(1, 6))
    l, u = sl*PI_LO/zh, su*PI_HI/z
    eta3 = half_minus((l*F(3, 52), u*F(3, 52)), three)
    eta4 = half_minus((PI_LO/(7*zh), PI_HI/(7*z)), catalan)
    eta6 = half_minus((l*F(9, 91), u*F(9, 91)), six)
    relation = (15*eta3[0]-4)/7, (15*eta3[1]-4)/7
    return (p, *three, c, *catalan, s, *six, p+prefix(3, N//2)/4, F(5, 4),
            three[0]*F(5, 4), three[1]*F(5, 4), tail, z, zh, sl, su, *eta3, *eta4, *eta6, *relation)


def inside(bounds, value, why):
    check(dec(bounds[0])-D('1e-43') <= value <= dec(bounds[1])+D('1e-43'), (why, bounds, value))


def main():
    ap = argparse.ArgumentParser();ap.add_argument('--driver', required=True);args = ap.parse_args()
    cases = list(dict.fromkeys((N, K) for N in range(1, 241) for K in (1, 241-N, 240)))
    cases += [(0, 1), (241, 1), (1, 0), (1, 241), (2**32-1, 1)]
    run = subprocess.run([str(Path(args.driver).absolute())], input=''.join(f'{N} {K}\n' for N, K in cases),
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = iter(run.stdout.splitlines());edge = next(lines).split()
    check(edge[0] == 'EDGES', 'edge report');edges = int(edge[1])
    three, catalan, six = full(3), full(4), full(6)
    check(abs(six-D('1.25')*three) < D('1e-43'), 'independent induced L2 factor')
    zeta = zeta_three();sqrt3 = D(3).sqrt()
    a3 = D('0.5')-3*sqrt3*PI*three/(52*zeta)
    a4 = D('0.5')-PI*catalan/(7*zeta)
    a6 = D('0.5')-9*sqrt3*PI*six/(91*zeta)
    check(abs(a6-(15*a3-4)/7) < D('1e-43'), 'independent small amplitude relation')
    finite_factor_witnesses = 0
    for N, K in cases:
        row = next(lines).split();valid = 1 <= N <= 240 and 1 <= K <= 240
        check(row[:2] == ['E', str(int(valid))], ('example admission', N, K))
        if not valid:
            check(len(row) == 2, 'failed examples empty');continue
        check(tuple(map(int, row[2:4])) == (N, K), 'example metadata')
        values = tuple(map(F, row[4:]));expected = reference(N, K)
        check(values == expected, ('exact example endpoints', N, K))
        check(all(str(F(x)) == x for x in row[4:]), 'canonical example endpoints')
        check(values[6] == values[9], ('literal finite induced cutoff identity', N, K))
        finite_factor_witnesses += values[6] != F(5, 4)*values[0]
        for bounds, actual, label in ((values[1:3], three, 'conductor-three L2'),
            (values[4:6], catalan, 'Catalan'), (values[7:9], six, 'induced conductor-six L2'),
            (values[11:13], six, 'full induced factor'), (values[16:18], sqrt3, 'sqrt three'),
            (values[18:20], a3, 'eta three'), (values[20:22], a4, 'eta four'),
            (values[22:24], a6, 'eta six direct'), (values[24:26], a6, 'eta six induced relation')):
            inside(bounds, actual, (label, N, K))
        check(max(values[22], values[24]) <= min(values[23], values[25]), 'two eta-six routes overlap')
    check(next(lines, None) is None, 'no extra driver records')
    check(finite_factor_witnesses > 0, 'full Euler factor not substituted for finite cutoff identity')
    print(f'PASS small-conductor examples: {checks} checks, {len(cases)} API cases, {edges} C edge checks, '
          f'{finite_factor_witnesses} finite-prefix distinctions; independent progression L-values and Decimal square root.')


if __name__ == '__main__':
    main()
