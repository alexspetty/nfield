#!/usr/bin/env python3
"""Independent decimal/series references for exact rational constant bounds."""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import subprocess

getcontext().prec = 100
KEYS = ('pi_lower pi_upper zeta_two_lower zeta_two_upper zeta_three_lower zeta_three_upper '
        'zeta_four_lower zeta_four_upper gamma_harmonic_prefix log_n_lower log_n_upper '
        'gamma_lower gamma_upper log_moment_prefix_lower log_moment_prefix_upper log_moment_tail_upper '
        'log_moment_lower log_moment_upper kappa_lower kappa_upper leading_lower leading_upper').split()
checks = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def dec(x):
    x = F(x)
    return D(x.numerator)/D(x.denominator)


def atan_inverse(n):
    return sum((D(-1 if k % 2 else 1)/(D(2*k+1)*D(n)**(2*k+1))
                for k in range(180)), D(0))


@lru_cache(None)
def log_reference(n):
    # Direct rational powers supply an endpoint reference independently of
    # the C recurrence. Decimal.ln separately checks the actual logarithm.
    b = n.bit_length()-1
    a = 2**b

    def polynomial(r):
        lo = 2*sum((r**(2*i+1)/F(2*i+1) for i in range(24)), F(0))
        return lo, lo+2*r**49/(1-r*r)

    two = polynomial(F(1, 3))
    reduced = polynomial(F(n-a, n+a))
    raw = (b*two[0]+reduced[0], b*two[1]+reduced[1])
    scale = 10**24
    lo = raw[0]*scale
    hi = raw[1]*scale
    return F(lo.numerator//lo.denominator, scale), F(-(-hi.numerator//hi.denominator), scale)


@lru_cache(None)
def constant_reference_table():
    midpoint = F(3141592653589793238465, 10**21)
    radius = F(1, 2*10**20)
    pl, ph = midpoint-radius, midpoint+radius
    z2l, z2h, z4l, z4h = pl*pl/6, ph*ph/6, pl**4/90, ph**4/90
    harmonic, cubic, moment_l, moment_h = F(0), F(0), F(0), F(0)
    references = {}
    for N in range(1, 241):
        ll, lh = log_reference(N)
        cubic += F(1, N**3)
        moment_l += ll/N**2
        moment_h += lh/N**2
        b = (2*N-1).bit_length()
        z3l, z3h = cubic, cubic+F(1, 2*N*N)
        gl = harmonic-lh+F(1, 2*N)
        gh = harmonic-ll+F(1, 2*N)+F(1, 12*N*N)
        tail = F(2*b+3, N)
        ml, mh = moment_l, moment_h+tail
        references[N] = dict(zip(KEYS, [pl, ph, z2l, z2h, z3l, z3h, z4l, z4h,
            harmonic, ll, lh, gl, gh, moment_l, moment_h, tail, ml, mh,
            gl+ml/z2h, gh+mh/z2l, z2l/z3h, z2h/z3l]))
        harmonic += F(1, N)

    return references


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    ap.add_argument('--bin')
    args = ap.parse_args()
    queries = [(op, n) for op in ('L', 'C') for n in range(242)]
    run = subprocess.run([str(Path(args.driver).resolve())],
                         input=''.join(f'{op} {n}\n' for op, n in queries),
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = run.stdout.splitlines()
    check(lines[0].startswith('EDGES '), lines[:1])
    edges = int(lines[0].split()[1])
    check(len(lines) == len(queries)+1, ('record count', len(lines)))

    pi = 16*atan_inverse(5)-4*atan_inverse(239)
    R = 4096
    harmonic_long = sum((D(1)/D(n) for n in range(1, R)), D(0))
    gamma_low = harmonic_long-D(R).ln()+D(1)/(2*D(R))
    gamma_high = gamma_low+D(1)/(12*D(R)**2)
    z3_low = sum((D(1)/D(n)**3 for n in range(1, R+1)), D(0))
    z3_high = z3_low+D(1)/(2*D(R)**2)
    moment_low = sum((D(n).ln()/D(n)**2 for n in range(1, R+1)), D(0))
    moment_high = moment_low+(2*D(R).ln()+3)/D(R)
    z2 = pi*pi/6
    full_references = {'pi': (pi, pi), 'zeta_two': (z2, z2),
                       'zeta_three': (z3_low, z3_high), 'zeta_four': (pi**4/90, pi**4/90),
                       'gamma': (gamma_low, gamma_high), 'log_moment': (moment_low, moment_high),
                       'kappa': (gamma_low+moment_low/z2, gamma_high+moment_high/z2),
                       'leading': (z2/z3_high, z2/z3_low)}
    references = constant_reference_table()

    log_values = {}
    for (op, n), line in zip(queries, lines[1:]):
        data = line.split()
        check(data[0] == op, ('operation', op, n, data[:2]))
        valid = 1 <= n <= 240
        check(int(data[1]) == valid, ('admission', op, n))
        if not valid:
            check(len(data) == 2, ('failure output', op, n))
            continue
        if op == 'L':
            check(len(data) == 4, ('log fields', n))
            lo, hi = map(F, data[2:])
            check((lo, hi) == log_reference(n), ('exact power/grid reference', n, lo, hi))
            check(dec(lo) <= D(n).ln() <= dec(hi), ('independent logarithm', n))
            check(0 <= lo <= hi and hi-lo < F(1, 10**21), ('log width and positivity', n))
            log_values[n] = lo, hi
        else:
            check(len(data) == 26, ('constant fields', n, len(data)))
            check(list(map(int, data[2:4])) == [n, (2*n-1).bit_length()], ('constant metadata', n))
            actual = dict(zip(KEYS, map(F, data[4:])))
            for k in KEYS:
                check(actual[k] == references[n][k], ('exact constant endpoint', n, k, actual[k], references[n][k]))
            for name, (rl, rh) in full_references.items():
                lo, hi = actual[name+'_lower'], actual[name+'_upper']
                check(lo <= hi, ('interval order', n, name))
                check(dec(lo) <= rh and rl <= dec(hi), ('independent full-value consistency', n, name))
            check(moment_low <= dec(actual['log_moment_upper']), ('later logarithmic series', n))
            check(dec(actual['log_moment_prefix_lower']) <= moment_low, ('positive logarithmic prefix', n))
    products = 0
    for a in range(1, 241):
        for b in range(1, 240//a+1):
            al, ah = log_values[a]
            bl, bh = log_values[b]
            pl, ph = log_values[a*b]
            check(al+bl <= ph and pl <= ah+bh, ('logarithm product compatibility', a, b))
            products += 1
    cli_cases = 0
    if args.bin:
        binary = str(Path(args.bin).absolute())
        for N in (1, 2, 30, 239, 240):
            cli = subprocess.run([binary, 'weighted-remainder-state', 'expansion-constants', str(N)],
                                 text=True, capture_output=True)
            check(cli.returncode == 0 and not cli.stderr, ('CLI constants exit', N, cli.stderr))
            values = dict(line.split('=', 1) for line in cli.stdout.splitlines() if '=' in line)
            check(set(values) == set(KEYS)|{'constant_cutoff', 'log_tail_binary_exponent'}, ('CLI constant fields', N))
            check(int(values['constant_cutoff']) == N and int(values['log_tail_binary_exponent']) == (2*N-1).bit_length(), ('CLI metadata', N))
            check({k: F(values[k]) for k in KEYS} == references[N], ('independent CLI endpoints', N))
            cli_cases += 1
        for argv in ([], ['0'], ['241'], ['-1'], ['+1'], ['1.0'], ['x'], [''], ['1', 'extra']):
            cli = subprocess.run([binary, 'weighted-remainder-state', 'expansion-constants', *argv], text=True, capture_output=True)
            check(cli.returncode == 1 and not cli.stdout and 'cutoff 1..240' in cli.stderr, ('CLI invalid constant input', argv))
            cli_cases += 1
    print(f'PASS: {checks} checks; {len(queries)} API records; {edges} C edge assertions; '
          f'{products} logarithm product checks; {cli_cases} CLI cases; all constants and logarithms through 240.')
    print('Independent Machin pi, Decimal logarithms, exact direct-power/grid references, '
          'and longer positive harmonic/zeta/logarithmic series through 4096. '
          'Finite consistency checks remain distinct from universal Lean containment.')


if __name__ == '__main__':
    main()
