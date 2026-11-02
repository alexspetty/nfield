#!/usr/bin/env python3
"""Cotangent prefixes, induced cutoffs and independent progression sums."""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
from pathlib import Path
import subprocess
from test_weighted_remainder_character import cotangent, product, delta, progressions, bernoulli, PI, PI_LO, PI_HI
from test_weighted_remainder_fourier import trig_reference, dec

getcontext().prec = 90
checks = 0
KEYS = ('residue_bound unit_residue_bound prefix_lower prefix_upper unit_prefix_lower unit_prefix_upper '
        'tail_upper unit_tail_upper lower upper unit_lower unit_upper gcd_prefix_lower gcd_prefix_upper '
        'mobius_prefix_lower mobius_prefix_upper gcd_lower gcd_upper mobius_lower mobius_upper '
        'zeta_lower zeta_upper delta harmonic_seed_lower harmonic_seed_upper eta_lower eta_upper').split()


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


@lru_cache(None)
def base(q, N):
    bound = unit_bound = F(0)
    pl = pu = ul = uu = F(0)
    # Reference ordering is by residue progressions, rather than n%q.
    for a in range(1, q):
        l, u = cotangent(F(a, q))
        bound = max(bound, abs(l), abs(u))
        mass = sum((F(1, n*n) for n in range(a, N+1, q)), F(0))
        pl += mass*l;pu += mass*u
        if gcd(a, q) == 1:
            unit_bound = max(unit_bound, abs(l), abs(u))
            ul += mass*l;uu += mass*u
    tail = bound/N if N else F(0)
    unit_tail = unit_bound/N if N else F(0)
    return (bound, unit_bound, pl, pu, ul, uu, tail, unit_tail,
            pl-tail if N else F(0), pu+tail if N else F(0),
            ul-unit_tail if N else F(0), uu+unit_tail if N else F(0))


@lru_cache(None)
def mu(n):
    return F(1) if n == 1 else -sum((mu(d) for d in range(1, n) if n % d == 0), F(0))


def scaled_add(a, b, c):
    t = product(b, (c, c))
    return a[0]+t[0], a[1]+t[1]


def reference(q, N, K):
    b = base(q, N)
    gp = mp = gf = mf = (F(0), F(0))
    for d in range(1, q+1):
        if q % d:
            continue
        gp = scaled_add(gp, base(d, N*d//q)[4:6], F(d*d, q*q))
        mp = scaled_add(mp, base(q//d, N//d)[2:4], mu(d)/F(d*d))
        gf = scaled_add(gf, base(d, N)[10:12], F(d*d, q*q))
        mf = scaled_add(mf, base(q//d, N)[8:10], mu(d)/F(d*d))
    zl = sum((F(1, n**3) for n in range(1, K+1)), F(0));zu = zl+F(1, 2*K*K)
    d = delta(q)
    c = F(q**3+1, 2*q**3)
    sub = product(b[8:10], (PI_LO/(2*q), PI_HI/(2*q)))
    seed = zl*c-sub[1], zu*c-sub[0]
    if q == 1:
        eta = F(1), F(1)
    else:
        sub = product(b[10:12], (PI_LO/(2*q*zu*d), PI_HI/(2*q*zl*d)))
        eta = F(1, 2)-sub[1], F(1, 2)-sub[0]
    return b+gp+mp+gf+mf+(zl, zu, d)+seed+eta


@lru_cache(None)
def actual(q, N):
    cp = up = cf = uf = D(0)
    for a in range(1, q):
        if 2*a == q:
            continue
        sine, cosine = trig_reference(F(a, q))
        cot = cosine/sine
        partial = sum((1/D(n*n) for n in range(a, N+1, q)), D(0))
        full = progressions(F(a, q))[1]/(q*q)
        cp += cot*partial;cf += cot*full
        if gcd(a, q) == 1:
            up += cot*partial;uf += cot*full
    return cp, up, cf, uf


def inside(bounds, x, why):
    check(dec(bounds[0])-D('1e-43') <= x <= dec(bounds[1])+D('1e-43'), (why, bounds, x))


def zeta_three():
    # Independent EM evaluation of the ordinary cubic series, at y=65.
    y = D(65)
    z = sum((1/D(n)**3 for n in range(1, 65)), D(0))+1/(2*y*y)+1/(2*y**3)
    for k in range(1, 17):
        z += dec(bernoulli[2*k])*(2*k+1)/(2*y**(2*k+2))
    return z


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    args = ap.parse_args()
    prefix = list(dict.fromkeys((q, N) for q in range(1, 241)
                               for N in (0, 1, q-1, q, min(240, q+1), 240)))
    prefix += [(0, 1), (241, 1), (3, 241), (2**32-1, 1)]
    full = [(q, 31, 29) for q in range(1, 241)]
    full += [(q, N, K) for q in (1, 2, 3, 4, 6, 8, 12, 24, 30, 40, 64, 120, 239, 240)
             for N, K in ((1, 240), (240, 1), (240, 240), (7, 13))]
    full += [(0, 1, 1), (241, 1, 1), (3, 0, 1), (3, 241, 1), (3, 1, 0), (3, 1, 241)]
    inputs = [f'P {q} {N} 0' for q, N in prefix]+[f'C {q} {N} {K}' for q, N, K in full]
    run = subprocess.run([str(Path(args.driver).absolute())], input='\n'.join(inputs)+'\n',
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = iter(run.stdout.splitlines())
    edge = next(lines).split();check(edge[0] == 'EDGES', 'edge report');edges = int(edge[1])
    for q, N in prefix:
        row = next(lines).split();valid = 1 <= q <= 240 and 0 <= N <= 240
        check(row[:2] == ['P', str(int(valid))], ('prefix admission', q, N))
        if not valid:
            check(len(row) == 2, 'failed prefix empty');continue
        expected = base(q, N)[2:6]
        check(tuple(map(F, row[2:])) == expected, ('exact progression prefix', q, N))
        check(all(str(F(x)) == x for x in row[2:]), ('canonical prefix', q, N))
        cp, up, _, _ = actual(q, N)
        inside(expected[:2], cp, ('direct finite cotangent prefix', q, N))
        inside(expected[2:], up, ('direct finite unit prefix', q, N))
    zeta = zeta_three()
    cutoff_witnesses = 0
    for q, N, K in full:
        row = next(lines).split();valid = 1 <= q <= 240 and 1 <= N <= 240 and 1 <= K <= 240
        check(row[:2] == ['C', str(int(valid))], ('full admission', q, N, K))
        if not valid:
            check(len(row) == 2, 'failed full empty');continue
        check(tuple(map(int, row[2:5])) == (q, N, K), ('full metadata', q, N, K))
        expected = reference(q, N, K);values = tuple(map(F, row[5:]))
        check(values == expected, ('exact full cotangent endpoints', q, N, K))
        check(all(str(F(x)) == x for x in row[5:]), ('canonical cotangent', q, N, K))
        cp, up, cf, uf = actual(q, N)
        inside(values[8:10], cf, ('independent full cotangent progression', q, N, K))
        inside(values[10:12], uf, ('independent full unit progression', q, N, K))
        inside(values[12:14], cp, ('finite gcd descent adjusted cutoffs', q, N, K))
        inside(values[14:16], up, ('finite Mobius inversion adjusted cutoffs', q, N, K))
        inside(values[16:18], cf, ('full gcd descent', q, N, K))
        inside(values[18:20], uf, ('full Mobius inversion', q, N, K))
        seed = zeta*(1+D(1)/D(q)**3)/2-PI*cf/(2*q)
        eta = D(1) if q == 1 else D('0.5')-PI*uf/(2*q*zeta*dec(delta(q)))
        inside(values[23:25], seed, ('harmonic root average', q, N, K))
        inside(values[25:27], eta, ('amplitude cotangent formula', q, N, K))
        if q in (6, 12, 24, 30, 40, 120, 240):
            wrong = sum(((D(d)/q)**2*actual(d, N)[1] for d in range(1, q+1) if q % d == 0), D(0))
            cutoff_witnesses += abs(wrong-cp) > D('1e-12')
        if q == 2:
            check(values[8:12] == (F(0),)*4 and values[25:] == (F(1, 2),)*2, 'exact modulus-two cotangent')
    check(next(lines, None) is None, 'no extra driver records')
    check(cutoff_witnesses > 0, 'wrong same-cutoff finite descent falsified')
    print(f'PASS cotangent series and divisor descent: {checks} checks, {len(prefix)} prefix API cases, '
          f'{len(full)} full API cases, {edges} C edge checks, {cutoff_witnesses} witnesses against '
          'same-cutoff finite descent; independent progression references and separate infinite tails.')


if __name__ == '__main__':
    main()
