#!/usr/bin/env python3
"""Spectral band/tail oracle: divisor inversion and direct finite DFT.

Exact endpoint checks and finite longer-prefix checks do not replace the
separate Lean theorem for the full infinite orthogonal projection error.
"""
import argparse
import cmath
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm, pi
from pathlib import Path
import subprocess
from test_weighted_remainder_constants import log_reference, constant_reference_table, dec
from test_weighted_remainder_spectral import divisors, mobius, h_reference, product_reference

getcontext().prec = 90
KEYS = ("product_lower product_upper amplitude_leading_lower amplitude_leading_upper "
        "log_q_lower log_q_upper log_b_lower log_b_upper weighted_band_lower weighted_band_upper "
        "weighted_remainder_upper weighted_tail_lower weighted_tail_upper energy_band_lower "
        "energy_band_upper energy_remainder_upper projection_tail_lower projection_tail_upper "
        "weighted_leading_lower weighted_leading_upper energy_leading_lower energy_leading_upper").split()
checks = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


@lru_cache(None)
def harmonic(n):
    return sum((F(1, a) for a in range(1, n+1)), F(0))


@lru_cache(None)
def weight(n):
    # Möbius inversion of the full harmonic sum, independent of C's unit loop.
    return sum((mobius(d)*harmonic(n//d-1)/d for d in divisors(n)), F(0))/n**2


@lru_cache(None)
def energy_reference(q, M):
    prefix = sum((weight(k) for k in range(q, M+1, q)), F(0))
    mass = sum((weight(k) for k in range(2, M+1)), F(0))
    upper = min(prefix+1-mass, prefix+F(2*(2*M-1).bit_length()+3, q*M),
                4*(1+log_reference(q)[1])/q**2)
    j2 = sum(mobius(d)*(q//d)**2 for d in divisors(q))
    return prefix, upper, j2*prefix**2/27, j2*upper**2/27


@lru_cache(None)
def band_reference(Q, B, M):
    wl = sum((h_reference(q)*log_reference(q)[0]**2/q**2 for q in range(Q+1, B+1)), F(0))
    wu = sum((h_reference(q)*log_reference(q)[1]**2/q**2 for q in range(Q+1, B+1)), F(0))
    el = sum((energy_reference(q, M)[2] for q in range(Q+1, B+1)), F(0))
    eu = sum((energy_reference(q, M)[3] for q in range(Q+1, B+1)), F(0))
    return wl, wu, el, eu


def tail_reference(Q, B, M, P, N):
    cl, cu = product_reference(P)
    constants = constant_reference_table()[N]
    al, au = constants['leading_lower'], constants['leading_upper']
    ql, qu = log_reference(Q)
    bl, bu = log_reference(B)
    wl, wu, el, eu = band_reference(Q, B, M)
    wr = (bu**2+2*bu+2)/B
    er = 32*(bu**2+2*bu+3)/(27*B)
    wll, wlu = cl*ql**2/Q, cu*qu**2/Q
    ell, elu = al**2*wll/27, au**2*wlu/27
    return dict(zip(KEYS, [cl, cu, al, au, ql, qu, bl, bu, wl, wu, wr, wl, wu+wr,
                           el, eu, er, el, eu+er, wll, wlu, ell, elu]))


def long_prefixes(R):
    # Separate divisor sieve, Decimal harmonic sums and signed convolutions.
    mu = [0]*(R+1)
    mu[1] = 1
    ds = [[] for _ in range(R+1)]
    for d in range(1, R+1):
        for n in range(d, R+1, d):
            ds[n].append(d)
            if n != d:
                mu[n] -= mu[d]
    H = [D(0)]
    for n in range(1, R+1):
        H.append(H[-1]+D(1)/n)
    w, h = [D(0)]*(R+1), [D(0)]*(R+1)
    for n in range(1, R+1):
        w[n] = sum((D(mu[d])*H[n//d-1]/d for d in ds[n]), D(0))/D(n)**2
        phi = sum(mu[d]*(n//d) for d in ds[n])
        j2 = sum(mu[d]*(n//d)**2 for d in ds[n])
        delta = sum((D(mu[d])/D(d)**3 for d in ds[n]), D(0))
        rho = D(phi)/n/delta
        h[n] = D(j2)*rho*rho/D(n)**2
        check(w[n] >= 0 and 0 < h[n] <= 1, ('long finite arithmetic', n))
    amplitudes = {q: sum(w[q::q], D(0)) for q in range(2, 241)}
    weighted = [D(0)]*(R+1)
    for q in range(R-1, -1, -1):
        weighted[q] = weighted[q+1]+h[q+1]*D(q+1).ln()**2/D(q+1)**2
    energies = {q: D(sum(mu[d]*(q//d)**2 for d in ds[q]))*amplitudes[q]**2/27 for q in range(2, 241)}
    return amplitudes, weighted, energies


def direct_projection_checks(energy_values):
    worst = 0.0
    count = 0
    for M in range(2, 9):
        L = lcm(*range(2, M+1))
        potential = [sum((F(2, 3)*weight(k)*(F(n % k)-F(k-1, 2)) for k in range(2, M+1)), F(0))
                     for n in range(L)]
        for q in range(2, M+1):
            # Direct characters of exact conductor q, applied to the finite
            # potential itself. No amplitude or Jordan formula constructs it.
            bins = [sum((potential[n] for n in range(r, L, q)), F(0))/L for r in range(q)]
            value = sum(abs(sum(float(bins[r])*cmath.exp(-2j*pi*r*a/q) for r in range(q)))**2
                        for a in range(1, q) if gcd(a, q) == 1)
            expected = float(energy_values[(q, M)][2])
            error = abs(value-expected)
            worst = max(worst, error)
            check(error < 5e-11, ('direct finite conductor projection', q, M, value, expected))
            count += 1
    return count, worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    ap.add_argument('--bin')
    args = ap.parse_args()
    energies = sorted(set([(q, M) for q in range(2, 241) for M in (2, 4, 7, 16, 63, 127, 240)] +
                          [(q, M) for M in range(2, 241) for q in (2, 17, 239)] +
                          [(q, M) for M in range(2, 9) for q in range(2, M+1)] +
                          [(1, 2), (241, 2), (2, 1), (2, 241)]))
    tails = [(Q, max(4, Q), 17, 127, 31) for Q in range(1, 241)]
    tails += [(Q, min(240, max(4, Q+1)), 63, 17, 7) for Q in range(1, 241)]
    tails += [(Q, 240, M, 239, 127) for Q in (1, 2, 7, 31, 127, 239, 240) for M in (2, 16, 240)]
    tails += [(31, 64, n, 17, 7) for n in range(2, 241)]
    tails += [(7, 8, 17, n, n) for n in range(1, 241)]
    tails += [(0, 4, 2, 1, 1), (5, 4, 2, 1, 1), (1, 3, 2, 1, 1), (1, 241, 2, 1, 1),
              (1, 4, 1, 1, 1), (1, 4, 241, 1, 1), (1, 4, 2, 0, 1), (1, 4, 2, 241, 1),
              (1, 4, 2, 1, 0), (1, 4, 2, 1, 241)]
    inputs = [f'E {q} {M}' for q, M in energies] + ['T '+' '.join(map(str, t)) for t in tails]
    run = subprocess.run([str(Path(args.driver).absolute())], input='\n'.join(inputs)+'\n',
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = run.stdout.splitlines()
    check(lines and lines[0].startswith('EDGES '), lines[:1])
    edges = int(lines[0].split()[1])
    check(len(lines) == len(inputs)+1, ('records', len(lines)))
    amplitude_long, weighted_long, energy_long = long_prefixes(2048)
    energy_values = {}
    for (q, M), line in zip(energies, lines[1:]):
        v = line.split()
        valid = 2 <= q <= 240 and 2 <= M <= 240
        check(v[:2] == ['E', str(int(valid))], ('energy admission', q, M))
        if not valid:
            check(len(v) == 2, ('invalid energy', q, M))
            continue
        actual = tuple(map(F, v[2:]))
        expected = energy_reference(q, M)
        check(actual == expected, ('independent energy endpoints', q, M, actual, expected))
        check(len(v) == 6 and all(str(F(x)) == x for x in v[2:]), ('canonical energy', q, M))
        check(0 <= actual[0] <= actual[1] and 0 <= actual[2] <= actual[3], ('energy order', q, M))
        check(dec(actual[0]) <= amplitude_long[q] <= dec(actual[1]), ('long finite amplitude', q, M))
        check(dec(actual[2]) <= energy_long[q] <= dec(actual[3]), ('long finite conductor energy', q, M))
        if q > M:
            check(actual[0] == actual[2] == 0, ('absent finite conductor', q, M))
        energy_values[(q, M)] = actual
    for params, line in zip(tails, lines[1+len(energies):]):
        Q, B, M, P, N = params
        v = line.split()
        valid = 1 <= Q <= B <= 240 and B >= 4 and 2 <= M <= 240 and 1 <= P <= 240 and 1 <= N <= 240
        check(v[:2] == ['T', str(int(valid))], ('tail admission', params))
        if not valid:
            check(len(v) == 2, ('invalid tail', params))
            continue
        check(list(map(int, v[2:8])) == [*params, (2*M-1).bit_length()], ('metadata', params))
        check(len(v) == 30, ('tail fields', params, len(v)))
        a = dict(zip(KEYS, map(F, v[8:])))
        expected = tail_reference(*params)
        for k in KEYS:
            check(a[k] == expected[k], ('exact tail endpoint', params, k, a[k], expected[k]))
        check(all(str(F(raw)) == raw for raw in v[8:]), ('canonical tail', params))
        for key in ('weighted_band', 'weighted_tail', 'energy_band', 'projection_tail', 'weighted_leading', 'energy_leading'):
            check(0 <= a[key+'_lower'] <= a[key+'_upper'], ('nonnegative intervals', params, key))
        check(dec(a['weighted_tail_lower']) <= weighted_long[Q] <= dec(a['weighted_tail_upper']), ('long weighted finite tail', params))
        band_long = sum((energy_long[q] for q in range(Q+1, B+1)), D(0))
        check(dec(a['energy_band_lower']) <= band_long <= dec(a['energy_band_upper']), ('long energy band', params))
        if Q == B:
            check(a['energy_band_upper'] == a['weighted_band_upper'] == 0, ('empty band', params))
        if Q == 1:
            check(a['weighted_leading_upper'] == a['energy_leading_upper'] == 0, ('leading term at one', params))
        # A finite leading term is not asserted to enclose the true tail.
    projections, worst = direct_projection_checks(energy_values)
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
                check(len(rows) == len(actual) and set(actual) == set(expected), ('CLI fields', words))
                for k, value in expected.items():
                    check(actual[k] == str(value), ('CLI endpoint', words, k))
                if words[0] == 'spectral-tail':
                    check('Leading terms are asymptotic readouts, not tail error bounds' in r.stdout, ('asymptotic boundary', words))
        for q, M in [(2, 2), (7, 2), (12, 17), (239, 240), (240, 240)]:
            a, b, c, d = energy_reference(q, M)
            invoke(['spectral-energy', str(q), str(M)], dict(conductor=q, period_cutoff=M,
                   amplitude_lower=a, amplitude_upper=b, energy_lower=c, energy_upper=d))
        for p in [(1, 4, 2, 1, 1), (4, 4, 2, 1, 1), (31, 127, 63, 17, 7), (239, 240, 240, 240, 240)]:
            Q, B, M, P, N = p
            expected = tail_reference(*p)
            expected.update(cutoff=Q, band_cutoff=B, period_cutoff=M, prime_cutoff=P,
                            constant_cutoff=N, period_binary_exponent=(2*M-1).bit_length())
            invoke(['spectral-tail', *map(str, p)], expected)
        for words in [['spectral-energy'], ['spectral-energy', '2'], ['spectral-energy', '2', '2', 'extra'],
                      ['spectral-tail'], ['spectral-tail', '1', '4', '2', '1'],
                      ['spectral-tail', '1', '4', '2', '1', '1', 'extra']]:
            invoke(words)
        for bad in ('0', '1', '241', '-2', '+2', '2.0', '2/1', '9'*160):
            invoke(['spectral-energy', bad, '2'])
            invoke(['spectral-energy', '2', bad])
        for p in tails[-10:]:
            invoke(['spectral-tail', *map(str, p)])
        for i in range(5):
            p = ['1', '4', '2', '1', '1']
            p[i] = '+4'
            invoke(['spectral-tail', *p])
    print(f'PASS spectral energy and tails: {checks} checks, {len(inputs)} API cases, '
          f'{edges} C edge checks, {projections} direct finite conductor projections, max error {worst:.3e}; '
          f'{cli_cases} CLI cases; infinite proofs remain separate.')


if __name__ == '__main__':
    main()
