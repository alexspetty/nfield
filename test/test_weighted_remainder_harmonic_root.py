#!/usr/bin/env python3
"""Harmonic power/root series, root average and finite sine transform.

Exact Gaussian powers and residue-bucket sums replay rational endpoints.
Independent long Decimal series check the analytic values and root identity;
the universal convergence and tail estimates remain separate Lean proofs.
"""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import subprocess
import sys
from test_weighted_remainder_complex import phase_reference
from test_weighted_remainder_character import product, add, scale, phase_decimal, cotangent, PI, PI_LO, PI_HI
from test_weighted_remainder_cotangent import zeta_three
from test_weighted_remainder_fourier import dec

getcontext().prec = 90
# Two 63-bit rational coordinates raised through degree 240 can produce
# more than 4,300 decimal digits. These are our bounded exact API outputs.
sys.set_int_max_str_digits(50000)
checks = 0
ZERO = (F(0),)*4
kernels = [F(0)]*241
H = F(0)
for n in range(1, 241):
    kernels[n] = H/F(n*n)
    H += F(1, n)


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def tail(N):
    return F(2*(2*N-1).bit_length()+3, N)


def gaussian_mul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def gaussian_power(z, n):
    # Independent binary exponentiation, not the C successive-power loop.
    result = F(1), F(0)
    while n:
        if n & 1:
            result = gaussian_mul(result, z)
        z = gaussian_mul(z, z)
        n //= 2
    return result


def polylog_reference(re, im, N):
    r = i = F(0)
    for n in range(1, N+1):
        a, b = gaussian_power((re, im), n)
        r += kernels[n]*a;i += kernels[n]*b
    radius = tail(N) if re or im else F(0)
    return (re, im, radius, r, r, i, i, r-radius, r+radius, i-radius, i+radius)


@lru_cache(None)
def long_polylog(re, im):
    z = dec(re), dec(im)
    p = D(1), D(0)
    r = i = h = D(0)
    for n in range(1, 4097):
        p = gaussian_mul(p, z)
        r += h*p[0]/(n*n);i += h*p[1]/(n*n)
        h += 1/D(n)
    return r, i


def root_reference(q, a, N, K):
    hp = ZERO
    cp = sp = (F(0), F(0))
    # Reference finite sums first group coefficients into residue buckets.
    hmass = [F(0)]*q;cmass = [F(0)]*q;smass = [F(0)]*q
    for n in range(1, N+1):
        r = a*n % q;hmass[r] += kernels[n];cmass[r] += F(1, n**3);smass[r] += F(1, n*n)
    for r in range(q):
        if not (hmass[r] or cmass[r] or smass[r]):
            continue
        phase = phase_reference(F(r, q))
        hp = add(hp, scale(phase, (hmass[r],)*2))
        cp = add(cp, (cmass[r]*phase[0], cmass[r]*phase[1]))
        sp = add(sp, (smass[r]*phase[2], smass[r]*phase[3]))
    ht, ct, st = tail(N), F(1, 2*N*N), F(1, N)
    hf = add(hp, (-ht, ht, -ht, ht));cf = cp[0]-ct, cp[1]+ct;sf = sp[0]-st, sp[1]+st
    zl = sum((F(1, n**3) for n in range(1, K+1)), F(0));zu = zl+F(1, 2*K*K)
    if a == 0:
        hf = max(hf[0], zl), min(hf[1], zu), F(0), F(0)
        cf = max(cp[0], zl), min(cf[1], zu);sf = F(0), F(0)
    angle = product((PI_LO, PI_HI), (F(2*a-q, 2*q),)*2)
    correction = product(angle, sf)
    identity = (zl+cf[0])/2+correction[0], (zu+cf[1])/2+correction[1]
    return (phase_reference(F(a, q))+hp+hf+
            (ht, *cp, ct, *cf, *sp, st, *sf, zl, zu, *angle, *identity))


@lru_cache(None)
def long_root(q, a):
    if a == 0:
        zeta = zeta_three()
        return zeta, D(0), zeta, D(0)
    phases = [phase_decimal(F(r, q)) for r in range(q)]
    hr = hi = cubic = sine = h = D(0)
    for n in range(1, 4097):
        re, im = phases[a*n % q]
        hr += h*re/(n*n);hi += h*im/(n*n)
        cubic += re/D(n)**3;sine += im/(n*n);h += 1/D(n)
    return hr, hi, cubic, sine


def inside(bounds, x, why, slack=D('1e-40')):
    check(dec(bounds[0])-slack <= x <= dec(bounds[1])+slack, (why, bounds, x))


def main():
    ap = argparse.ArgumentParser();ap.add_argument('--driver', required=True);args = ap.parse_args()
    points = [(F(0), F(0)), (F(1), F(0)), (F(-1), F(0)), (F(0), F(1)), (F(0), F(-1)),
              (F(3, 5), F(4, 5)), (F(-3, 5), F(4, 5)), (F(1, 3), F(-2, 7)),
              (F(2**62, 2**63-1), F(0)), (F(1, 2**62), F(1, 2**62))]
    polys = [(N, re, im) for re, im in points for N in (1, 13, 240)]
    polys += [(0, F(0), F(0)), (241, F(0), F(0)), (1, F(3, 4), F(3, 4)),
              (1, F(1, 2**63), F(0)), (1, F(2**63), F(0))]
    roots = [(q, q//3, 31, 29) for q in range(1, 241)]
    roots += [(q, a, N, K) for q in (1, 2, 3, 4, 6, 8, 12, 24, 40, 120, 239, 240)
              for a in {0, q//2, q-1} for N, K in ((1, 240), (240, 1), (240, 240))]
    roots += [(0, 0, 1, 1), (241, 0, 1, 1), (3, 3, 1, 1), (3, 1, 0, 1),
              (3, 1, 241, 1), (3, 1, 1, 0), (3, 1, 1, 241)]
    averages = [(q, 31) for q in range(1, 241)]
    averages += [(q, N) for q in (1, 2, 6, 12, 24, 40, 120, 240) for N in (1, 240)]
    averages += [(0, 1), (241, 1), (3, 0), (3, 241)]
    sines = [(q, n) for q in range(1, 241) for n in (0, 1, q//2, q, -q-1)]
    sines += [(q, n) for q in (1, 2, 3, 4, 6, 8, 12, 24, 40, 120, 239, 240)
              for n in (10**200+17, -10**200-19)]
    sines += [(0, 1), (241, 1)]
    requests = [f'H {N} {re} {im}' for N, re, im in polys]
    requests += [f'R {q} {a} {N} {K}' for q, a, N, K in roots]
    requests += [f'A {q} {N}' for q, N in averages]+[f'S {q} {n}' for q, n in sines]
    run = subprocess.run([str(Path(args.driver).absolute())], input='\n'.join(requests)+'\n',
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = iter(run.stdout.splitlines());edge = next(lines).split()
    check(edge[0] == 'EDGES', 'edge report');edges = int(edge[1])
    for N, re, im in polys:
        row = next(lines).split()
        valid = 1 <= N <= 240 and re*re+im*im <= 1 and all(
            abs(v.numerator).bit_length() <= 63 and v.denominator.bit_length() <= 63 for v in (re, im))
        check(row[:2] == ['H', str(int(valid))], ('polylog admission', N, re, im))
        if not valid:
            check(len(row) == 2, 'failed polylog empty');continue
        check(tuple(map(int, row[2:4])) == (N, (2*N-1).bit_length()), 'polylog metadata')
        values = tuple(map(F, row[4:]));expected = polylog_reference(re, im, N)
        check(values == expected, ('exact Gaussian power prefix', N, re, im))
        check(all(str(F(x)) == x for x in row[4:]), 'canonical polylog endpoints')
        lr, li = long_polylog(re, im)
        inside(values[7:9], lr, ('long harmonic power real', N, re, im))
        inside(values[9:11], li, ('long harmonic power imaginary', N, re, im))
    zeta = zeta_three()
    for q, a, N, K in roots:
        row = next(lines).split();valid = 1 <= q <= 240 and a < q and 1 <= N <= 240 and 1 <= K <= 240
        check(row[:2] == ['R', str(int(valid))], ('root admission', q, a, N, K))
        if not valid:
            check(len(row) == 2, 'failed root empty');continue
        check(tuple(map(int, row[2:7])) == (q, a, N, K, (2*N-1).bit_length()), 'root metadata')
        values = tuple(map(F, row[7:]));expected = root_reference(q, a, N, K)
        check(values == expected, ('exact root series and identity endpoints', q, a, N, K))
        check(all(str(F(x)) == x for x in row[7:]), 'canonical root endpoints')
        hr, hi, cubic, sine = long_root(q, a)
        inside(values[8:10], hr, ('long boundary harmonic real', q, a, N, K))
        inside(values[10:12], hi, ('long boundary harmonic imaginary', q, a, N, K))
        inside(values[16:18], cubic, ('long cubic cosine', q, a, N, K))
        inside(values[21:23], sine, ('long quadratic sine', q, a, N, K))
        inside(values[27:29], hr, ('root identity actual harmonic value', q, a, N, K))
        rhs = (zeta+cubic)/2+PI*(D(a)/q-D('0.5'))*sine
        check(abs(rhs-hr) <= dec(tail(4096))+PI/D(4096)+D('1e-30'), ('independent long root identity', q, a))
        check(max(values[8], values[27]) <= min(values[9], values[28]), 'harmonic/identity intervals overlap')
    for q, N in averages:
        row = next(lines).split();valid = 1 <= q <= 240 and 1 <= N <= 240
        check(row[:2] == ['A', str(int(valid))], ('average admission', q, N))
        if not valid:
            check(len(row) == 2, 'failed average empty');continue
        check(tuple(map(int, row[2:5])) == (q, N, (2*N-1).bit_length()), 'average metadata')
        # Independent n-first root sums; C sums a-first residue buckets.
        average = ZERO
        for n in range(1, N+1):
            if not kernels[n]:
                continue
            root_sum = ZERO
            for a in range(q):
                root_sum = add(root_sum, phase_reference(F(a*n % q, q)))
            average = add(average, scale(root_sum, (kernels[n]/q,)*2))
        selected = sum((kernels[n] for n in range(q, N+1, q)), F(0))
        values = tuple(map(F, row[5:]))
        check(values == average+(selected, tail(N), selected, selected+tail(N)), ('exact root average', q, N))
        check(average[0] <= selected <= average[1] and average[2] <= 0 <= average[3], ('literal finite root filter', q, N))
        check(all(str(F(x)) == x for x in row[5:]), 'canonical average endpoints')
    for q, n in sines:
        row = next(lines).split();valid = 1 <= q <= 240
        check(row[:2] == ['S', str(int(valid))], ('sine admission', q, n))
        if not valid:
            check(len(row) == 2, 'failed sine empty');continue
        r = n % q
        if not r:
            expected = (F(0),)*4
        else:
            lo = hi = F(0)
            for a in range(1, q):
                phase = phase_reference(F(a*r % q, q));v = product(phase[2:], (F(2*a-q, 2*q),)*2)
                lo += v[0];hi += v[1]
            cl, cu = cotangent(F(r, q));expected = lo, hi, -cu/2, -cl/2
        values = tuple(map(F, row[2:]))
        check(values == expected, ('exact finite sine and cotangent endpoints', q, n))
        check(all(str(F(x)) == x for x in row[2:]), 'canonical sine endpoints')
        check(max(values[0], values[2]) <= min(values[1], values[3]), ('literal sine identity intervals', q, n))
    check(next(lines, None) is None, 'no extra driver records')
    print(f'PASS harmonic/root series and sine transform: {checks} checks, {len(polys)} polylog, '
          f'{len(roots)} root, {len(averages)} root-average, {len(sines)} sine API cases; '
          f'{edges} C edge checks; exact Gaussian powers, root filters and independent long series.')


if __name__ == '__main__':
    main()
