#!/usr/bin/env python3
"""Exact rectangle replay plus independent periodic L-values.

Generic subgroup characters are independent of the C CRT table. Digamma
and trigamma progression sums, evaluated by a separately implemented
Euler--Maclaurin expansion, check actual L(1) and L(2) values. They are
numerical reference checks, not infinite-proof evidence. Full cotangent
moments also use these progression sums, separately from character products.
"""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import comb, gcd
from pathlib import Path
import subprocess
from test_weighted_remainder_complex import phase_reference, unit_characters, conductor
from test_weighted_remainder_fourier import exact_grid_reference, trig_reference, dec

getcontext().prec = 90
checks = 0
PI_LO = F('3.141592653589793238460')
PI_HI = F('3.141592653589793238470')
PI = D('3.141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825')
ZERO = (F(0),)*4


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def product(a, b):
    v = [x*y for x in a for y in b]
    return min(v), max(v)


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def scale(a, b):
    return (*product(a[:2], b), *product(a[2:], b))


def multiply(a, b):
    rr, ii = product(a[:2], b[:2]), product(a[2:], b[2:])
    ri, ir = product(a[:2], b[2:]), product(a[2:], b[:2])
    return rr[0]-ii[1], rr[1]-ii[0], ri[0]+ir[0], ri[1]+ir[1]


@lru_cache(None)
def cotangent(r):
    sl, su, cl, cu = exact_grid_reference(r.denominator, r.numerator)
    return product((cl, cu), (1/su, 1/sl))


@lru_cache(None)
def phase_decimal(r):
    if r == 0:
        return D(1), D(0)
    if r == F(1, 2):
        return D(-1), D(0)
    sine, cosine = trig_reference(2*r)
    return cosine, sine


def dproduct(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


bernoulli = [F(1)]
for n in range(1, 35):
    bernoulli.append(-sum(F(comb(n+1, k))*bernoulli[k] for k in range(n))/F(n+1))


@lru_cache(None)
def progressions(r):
    """psi(r), sum_(j>=0) 1/(r+j)^2; 16 EM terms after 64 shifts."""
    x = dec(r)
    y = x+64
    psi = y.ln()-1/(2*y)
    square = 1/y+1/(2*y*y)
    for k in range(1, 17):
        B = dec(bernoulli[2*k])
        psi -= B/(2*k*y**(2*k))
        square += B/y**(2*k+1)
    for j in range(64):
        psi -= 1/(x+j)
        square += 1/(x+j)**2
    # The positive-real EM remainder is at most the next term in magnitude.
    check(abs(dec(bernoulli[34])/(34*y**34)) < D('1e-48'), ('digamma reference remainder', r))
    check(abs(dec(bernoulli[34])/y**35) < D('1e-48'), ('trigamma reference remainder', r))
    return psi, square


def contains(rect, z, why, slack=D('1e-43')):
    check(dec(rect[0])-slack <= z[0] <= dec(rect[1])+slack and
          dec(rect[2])-slack <= z[1] <= dec(rect[3])+slack, (why, rect, z))


@lru_cache(None)
def character_reference(q, phases, N):
    coefficient, partial = ZERO, ZERO
    l_one, l_two = [D(0), D(0)], [D(0), D(0)]
    for a, r in enumerate(phases):
        if r < 0:
            continue
        value = phase_reference(r)
        conjugate = value[0], value[1], -value[3], -value[2]
        coefficient = add(coefficient, scale(conjugate, cotangent(F(a, q))))
        chi = phase_decimal(r)
        psi, square = progressions(F(a, q))
        l_one[0] -= chi[0]*psi/q
        l_one[1] += chi[1]*psi/q
        l_two[0] += chi[0]*square/(q*q)
        l_two[1] += chi[1]*square/(q*q)
    for n in range(1, N+1):
        r = phases[n % q]
        if r >= 0:
            partial = add(partial, scale(phase_reference(r), (F(1, n*n),)*2))
    one = scale(coefficient, (PI_LO/(2*q), PI_HI/(2*q)))
    two = add(partial, (-F(1, N), F(1, N), -F(1, N), F(1, N)))
    result = multiply(one, two)
    contains(one, l_one, ('ordered L1 via digamma progressions', q, phases, N))
    contains(two, l_two, ('L2 via trigamma progressions', q, phases, N))
    contains(result, dproduct(l_one, l_two), ('actual complex product', q, phases, N))
    return coefficient, one, partial, two, result


@lru_cache(None)
def generic(q):
    units, chars = unit_characters(q)
    return units, {tuple(chi.get(a, F(-1)) for a in range(q)): conductor(q, chi)
                   for chi in chars if chi[q-1] == F(1, 2)}


@lru_cache(None)
def weight(n):
    return sum((F(1, 2*a*(n-a)*n) for a in range(1, n) if gcd(a, n) == 1), F(0))


@lru_cache(None)
def delta(q):
    # Proper-divisor Jordan inversion, separate from the C Euler product.
    jordan = {1: 1}
    for n in range(2, q+1):
        if q % n == 0:
            jordan[n] = n**3-sum(v for d, v in jordan.items() if n % d == 0)
    return F(jordan[q], q**3)


@lru_cache(None)
def full_cotangent(q):
    result = D(0)
    for a in range(1, q):
        if gcd(a, q) != 1:
            continue
        sine, cosine = trig_reference(F(a, q))
        result += cosine/sine*progressions(F(a, q))[1]/(q*q)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    args = ap.parse_args()
    families = [(q, 31) for q in range(3, 33)]
    families += [(q, N) for q in (3, 4, 6, 8, 12, 16, 24, 40, 64, 120, 128, 240) for N in (1, 240)]
    mixtures = [(q, 31, 29, 37) for q in range(2, 241)]
    mixtures += [(q, N, K, M) for q in (2, 3, 4, 6, 8, 12, 24, 40, 120, 239, 240)
                 for N, K, M in ((1, 240, 2), (240, 1, 239), (240, 240, 240))]
    invalid = [(0, 1, 1, 2), (1, 1, 1, 2), (241, 1, 1, 2), (2, 0, 1, 2),
               (2, 241, 1, 2), (2, 1, 0, 2), (2, 1, 241, 2), (2, 1, 1, 0), (2, 1, 1, 241)]
    requests = [f'A {q} {N} 0 0' for q, N in families]
    requests += [f'M {q} {N} {K} {M}' for q, N, K, M in mixtures+invalid]
    run = subprocess.run([str(Path(args.driver).absolute())], input='\n'.join(requests)+'\n',
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = iter(run.stdout.splitlines())
    edge = next(lines).split();check(edge[0] == 'EDGES', 'edge report');edges = int(edge[1])
    character_cases = induced = 0
    for q, N in families:
        _, wanted = generic(q)
        header = next(lines).split()
        check(header == ['A', '1', str(len(wanted))], ('all odd family', q, N))
        seen = set()
        for _ in wanted:
            row = next(lines).split()
            check(row[0] == 'R' and len(row) == 27+q, ('character record width', q, N, len(row)))
            q1, index, level, denominator, N1 = map(int, row[1:6])
            phases = tuple(F(-1) if int(x) < 0 else F(int(x), denominator) for x in row[6:6+q])
            check((q1, N1) == (q, N) and index < q and phases in wanted and phases not in seen,
                  ('actual character identity', q, N, index))
            check(level == wanted[phases], ('induced conductor', q, N, index))
            seen.add(phases);induced += level < q
            values = tuple(map(F, row[6+q:]));expected = character_reference(q, phases, N)
            check(values == tuple(x for rect in expected for x in rect)+(F(1, N),),
                  ('exact character rectangles', q, N, index))
            check(all(str(F(x)) == x for x in row[6+q:]), ('canonical character endpoints', q, N, index))
            character_cases += 1
        check(seen == set(wanted), ('all odd and induced retained', q, N))
    for q, N, K, M in mixtures+invalid:
        row = next(lines).split();valid = 2 <= q <= 240 and 1 <= N <= 240 and 1 <= K <= 240 and 2 <= M <= 240
        check(row[:2] == ['M', str(int(valid))], ('mixed admission', q, N, K, M))
        if not valid:
            check(len(row) == 2, 'rejected mixed emits no fields');continue
        units, chars = generic(q)
        check(tuple(map(int, row[2:9])) == (q, N, K, M, len(units), len(chars), sum(d < q for d in chars.values())),
              ('mixed metadata', q, N, K, M))
        mixed = ZERO
        for chi in chars:
            mixed = add(mixed, character_reference(q, chi, N)[-1])
        d = delta(q);zl = sum((F(1, n**3) for n in range(1, K+1)), F(0));zu = zl+F(1, 2*K*K)
        dl, du = zl*d*len(units), zu*d*len(units)
        quotient = product(mixed[:2], (1/du, 1/dl))
        el, eu = F(1, 2)-quotient[1], F(1, 2)-quotient[0]
        mass = sum((weight(n) for n in range(2, M+1)), F(0))
        al = sum((weight(n) for n in range(q, M+1, q)), F(0));au = al+1-mass
        expected = mixed+(d, zl, zu, dl, du, el, eu, max(al, el), min(au, eu))
        values = tuple(map(F, row[9:]))
        check(values == expected, ('exact full mixed output', q, N, K, M))
        check(all(str(F(x)) == x for x in row[9:]), ('canonical mixed endpoints', q, N, K, M))
        actual = PI*len(units)/(2*q)*full_cotangent(q)
        contains(mixed, (actual, D(0)), ('independent periodic cotangent moment', q, N, K, M))
        check(expected[-2] <= expected[-1], ('positive/mixed amplitude intersection', q, N, K, M))
        if q == 2:
            check(mixed == ZERO and el == eu == F(1, 2), 'literal modulus-two empty odd sum')
    check(next(lines, None) is None, 'no extra driver records')
    check(induced > 0, 'induced character products tested')
    print(f'PASS character L-values and mixed moments: {checks} checks, {character_cases} character API cases, '
          f'{len(mixtures)+len(invalid)} mixed API cases, {edges} C edge checks, '
          f'{induced} induced odd character cases; generic unit groups and independent progression L-values.')


if __name__ == '__main__':
    main()
