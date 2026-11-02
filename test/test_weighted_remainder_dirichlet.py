#!/usr/bin/env python3
"""Independent deficit coefficients, rational intervals and positive series."""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import subprocess
from test_weighted_remainder_power import power_reference
from test_weighted_remainder_constants import constant_reference_table, atan_inverse

getcontext().prec = 100
KEYS = ('exponent zeta_prefix_lower zeta_prefix_upper zeta_tail_upper zeta_lower zeta_upper '
        'doubled_prefix_lower doubled_prefix_upper doubled_tail_upper doubled_lower doubled_upper '
        'prefix_lower prefix_upper formula_lower formula_upper special_lower special_upper lower upper tail_upper').split()
DIAGNOSTIC_KEYS = ('two_weight three_halves_weight loss_lower loss_upper margin_lower margin_upper '
                   'literal_loss_bound literal_margin').split()
checks = 0
R = 2048


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def dec(x):
    x = F(x)
    return D(x.numerator)/D(x.denominator)


@lru_cache(None)
def deficits():
    # Proper-divisor inversion computes mu, then the number of squarefree
    # divisors. No production prime-factor count is reused.
    mu = [0]*(R+1)
    mu[1] = 1
    for n in range(1, R+1):
        for multiple in range(2*n, R+1, n):
            mu[multiple] -= mu[n]
    counts = [0]*(R+1)
    for d in range(1, R+1):
        for n in range(d, R+1, d):
            counts[n] += abs(mu[d])
    return [0, 0]+[counts[n]//2-1 for n in range(2, R+1)]


@lru_cache(None)
def dirichlet_reference_table(s):
    coefficient = deficits()
    zlo = zhi = tlo = thi = plo = phi = F(0)
    constants = constant_reference_table()[1]
    table = {}
    for N in range(1, 241):
        lo, hi = power_reference(N, s)
        zlo += lo
        zhi += hi
        plo += coefficient[N]*lo
        phi += coefficient[N]*hi
        lo, hi = power_reference(N, 2*s)
        tlo += lo
        thi += hi
        ztail = power_reference(N, s-1)[1]/(s-1)
        ttail = power_reference(N, 2*s-1)[1]/(2*s-1)
        zl, zh, tl, th = zlo, zhi+ztail, tlo, thi+ttail
        fl, fh = zl**2/(2*th)-zh+F(1, 2), zh**2/(2*tl)-zl+F(1, 2)
        sl = sh = F(0)
        specialization = 0
        if s == 2:
            specialization = 2
            sl = F(7, 4)-constants['zeta_two_upper']
            sh = min(F(1, 8), F(7, 4)-constants['zeta_two_lower'])
        elif s == F(3, 2):
            specialization = 3
            sh = F(67, 80)
        lower, upper = max(F(0), plo, fl), fh
        if specialization:
            lower, upper = max(lower, sl), min(upper, sh)
        table[N] = specialization, dict(zip(KEYS,
            [s, zlo, zhi, ztail, zl, zh, tlo, thi, ttail, tl, th, plo, phi,
             fl, fh, sl, sh, lower, upper, upper-plo]))
    return table


@lru_cache(None)
def logarithms():
    return [D(0)]+[D(n).ln() for n in range(1, R+2)]


@lru_cache(None)
def numerical_zeta(s):
    x = dec(s)
    logs = logarithms()
    prefix = sum(((-x*logs[n]).exp() for n in range(1, R+1)), D(0))
    # Separate lower/upper integral remainders for the longer positive sum.
    lo = prefix+((1-x)*logs[R+1]).exp()/(x-1)
    hi = prefix+((1-x)*logs[R]).exp()/(x-1)
    return lo, hi


@lru_cache(None)
def numerical_deficit(s):
    zl, zh = numerical_zeta(s)
    tl, th = numerical_zeta(2*s)
    lo, hi = zl*zl/(2*th)-zh+D('0.5'), zh*zh/(2*tl)-zl+D('0.5')
    values = []
    total = D(0)
    x = dec(s)
    for n in range(1, R+1):
        total += D(deficits()[n])*(-x*logarithms()[n]).exp()
        if n <= 240:
            values.append(total)
    if s == 2:
        pi = 16*atan_inverse(5)-4*atan_inverse(239)
        lo = hi = D(7)/4-pi*pi/6
    return lo, hi, total, values


def parse_series(data, s, N):
    check(len(data) == 22, ('series field count', s, N, len(data)))
    specialization, reference = dirichlet_reference_table(s)[N]
    check(list(map(int, data[:2])) == [N, specialization], ('series metadata', s, N))
    actual = dict(zip(KEYS, map(F, data[2:])))
    for k in KEYS:
        check(actual[k] == reference[k], ('rational endpoint', s, N, k, actual[k], reference[k]))
    for name in ('zeta_prefix', 'zeta', 'doubled_prefix', 'doubled', 'prefix', 'formula', 'special', ''):
        p = name+'_' if name else ''
        check(actual[p+'lower'] <= actual[p+'upper'], ('ordered interval', s, N, name))
    check(0 <= actual['prefix_lower'] <= actual['lower'] <= actual['upper'], ('positive full lower', s, N))
    check(actual['tail_upper'] >= 0, ('nonnegative omitted bound', s, N))
    alo, ahi, long, prefixes = numerical_deficit(s)
    tolerance = max(D(1), abs(alo), abs(ahi))*D('1e-88')
    check(dec(actual['lower']) <= ahi+tolerance and alo <= dec(actual['upper'])+tolerance,
          ('long independent full interval consistency', s, N))
    check(long <= dec(actual['upper'])+tolerance, ('later positive deficit sum', s, N))
    check(dec(actual['prefix_lower'])-tolerance <= prefixes[N-1] <= dec(actual['prefix_upper'])+tolerance,
          ('independent retained prefix', s, N))
    check(long-prefixes[N-1] <= dec(actual['tail_upper'])+tolerance,
          ('later omitted positive sum', s, N))
    if s == 2:
        check(actual['prefix_lower'] == actual['prefix_upper'], ('exact s=2 prefix', N))
        check(actual['upper'] <= F(1, 8), ('s=2 stated strict bound closure', N))
    if s == F(3, 2):
        check(actual['upper'] <= F(67, 80), ('s=3/2 stated strict bound closure', N))
    return actual


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    ap.add_argument('--bin')
    args = ap.parse_args()
    exponents = sorted(set([F(j, 2) for j in range(3, 13)]+
                          [F(10, 7), F(7, 3), F(101, 100), F(599, 100)]))
    series = {(s, N) for s in exponents for N in (1, 2, 6, 30, 120, 240)}
    series |= {(s, N) for s in (F(3, 2), F(2), F(10, 7)) for N in range(1, 241)}
    series |= {(s, N) for s in [F(2**200+1, 2**200), F(2**254+1, 2**253)] for N in (1, 6, 240)}
    queries = [('C', N, None) for N in range(242)]
    queries += [('S', N, s) for s, N in sorted(series)]
    queries += [('D', N, None) for N in range(242)]
    queries += [('S', N, s) for s, N in [(F(2), 0), (F(2), 241), (F(1), 1), (F(601, 100), 1),
                 (F(-2), 1), (F(2**255+1, 2**254), 1), (F(2**256+1, 2**255), 1)]]
    commands = ''.join(f'{op} {N}'+(f' {s}' if op == 'S' else '')+'\n' for op, N, s in queries)
    run = subprocess.run([str(Path(args.driver).absolute())], input=commands, text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = run.stdout.splitlines()
    check(lines[0].startswith('EDGES '), lines[:1])
    edges = int(lines[0].split()[1])
    check(len(lines) == len(queries)+1, ('record count', len(lines)))
    diagnostics = 0
    for (op, N, s), line in zip(queries, lines[1:]):
        data = line.split()
        valid = 0 <= N <= 240 if op == 'C' else 1 <= N <= 240
        if op == 'S':
            valid = valid and 1 < s <= 6 and s.numerator.bit_length() <= 255 and s.denominator.bit_length() <= 255
        check(data[:2] == [op, str(int(valid))], ('admission', op, N, s, data[:2]))
        if not valid:
            check(len(data) == 2, ('failure record', op, N, s))
            continue
        if op == 'C':
            check(len(data) == 3 and F(data[2]) == deficits()[N], ('independent divisor inversion', N))
        elif op == 'S':
            parse_series(data[2:], s, N)
        else:
            check(len(data) == 54, ('diagnostic fields', N, len(data)))
            two = parse_series(data[2:24], F(2), N)
            three = parse_series(data[24:46], F(3, 2), N)
            actual = dict(zip(DIAGNOSTIC_KEYS, map(F, data[46:])))
            losslo = F(3, 2)*two['lower']+F(37, 100)*three['lower']
            losshi = F(3, 2)*two['upper']+F(37, 100)*three['upper']
            ref = [F(3, 2), F(37, 100), losslo, losshi, 1-losshi, 1-losslo, F(3979, 8000), F(4021, 8000)]
            check(list(actual.values()) == ref, ('literal weighted endpoint', N))
            check(actual['loss_upper'] <= actual['literal_loss_bound'], ('display loss bound', N))
            check(actual['margin_lower'] >= actual['literal_margin'] > F(1, 2), ('display strict margin', N))
            diagnostics += 1
    cli_cases = 0
    if args.bin:
        binary = str(Path(args.bin).absolute())

        def series_values(values, s, N, prefix=''):
            specialization, reference = dirichlet_reference_table(s)[N]
            expected_keys = set(KEYS)|{'cutoff', 'specialization'}
            if not specialization:
                expected_keys -= {'special_lower', 'special_upper'}
            for k in expected_keys:
                target = N if k == 'cutoff' else specialization if k == 'specialization' else reference[k]
                check(F(values[prefix+k]) == target, ('CLI exact series field', s, N, prefix+k))
            return {prefix+k for k in expected_keys}

        for spelling, N in [('3/2', 1), ('6/4', 240), ('2', 240), ('10/7', 30), ('6', 240),
                            ('101/100', 1), ('599/100', 240), ('02', 6)]:
            cli = subprocess.run([binary, 'weighted-remainder-state', 'deficit-series', spelling, str(N)], text=True, capture_output=True)
            check(cli.returncode == 0 and not cli.stderr, ('CLI series exit', spelling, N, cli.stderr))
            values = dict(line.split('=', 1) for line in cli.stdout.splitlines() if '=' in line)
            keys = series_values(values, F(spelling), N)
            check(set(values) == keys, ('CLI series field visibility', spelling, N))
            cli_cases += 1
        for N in (1, 2, 30, 239, 240):
            cli = subprocess.run([binary, 'weighted-remainder-state', 'deficit-diagnostic', str(N)], text=True, capture_output=True)
            check(cli.returncode == 0 and not cli.stderr, ('CLI diagnostic exit', N, cli.stderr))
            values = dict(line.split('=', 1) for line in cli.stdout.splitlines() if '=' in line)
            keys = series_values(values, F(2), N, 'two_')|series_values(values, F(3, 2), N, 'three_halves_')
            two, three = dirichlet_reference_table(F(2))[N][1], dirichlet_reference_table(F(3, 2))[N][1]
            ll = F(3, 2)*two['lower']+F(37, 100)*three['lower']
            lh = F(3, 2)*two['upper']+F(37, 100)*three['upper']
            expected = [F(3, 2), F(37, 100), ll, lh, 1-lh, 1-ll, F(3979, 8000), F(4021, 8000)]
            check([F(values[k]) for k in DIAGNOSTIC_KEYS] == expected, ('CLI diagnostic endpoints', N))
            check(set(values) == keys|set(DIAGNOSTIC_KEYS), ('CLI diagnostic field visibility', N))
            cli_cases += 1
        bad_series = [[], ['3/2'], ['3/2', '0'], ['3/2', '241'], ['1', '1'], ['7', '1'], ['1.5', '1'],
                      ['+3/2', '1'], ['-3/2', '1'], ['3/-2', '1'], ['3/0', '1'], ['3//2', '1'],
                      ['/2', '1'], ['3/', '1'], ['3/2/1', '1'], ['', '1'], [' 3/2', '1'], ['x', '1'],
                      ['0'*160+'2', '1'], [str(F(2**255+1, 2**254)), '1'], ['3/2', '1', 'extra']]
        for argv in bad_series:
            cli = subprocess.run([binary, 'weighted-remainder-state', 'deficit-series', *argv], text=True, capture_output=True)
            check(cli.returncode == 1 and not cli.stdout and 'rational exponent' in cli.stderr, ('CLI invalid series', argv))
            cli_cases += 1
        for argv in ([], ['0'], ['241'], ['-1'], ['+1'], ['1.0'], ['x'], [''], ['1', 'extra']):
            cli = subprocess.run([binary, 'weighted-remainder-state', 'deficit-diagnostic', *argv], text=True, capture_output=True)
            check(cli.returncode == 1 and not cli.stdout and 'cutoff 1..240' in cli.stderr, ('CLI invalid diagnostic', argv))
            cli_cases += 1
    print(f'PASS: {checks} checks; {len(queries)} API records; {edges} C edge assertions; '
          f'{len(series)} series cases; {diagnostics} weighted positivity diagnostics; {cli_cases} CLI cases.')
    print('Independent Mobius inversion and squarefree-divisor counts, exact power/grid endpoints, '
          'Machin pi, and longer positive Decimal series with integral tails through 2048. '
          'The universal zeta identity, infinite tail enclosure and strict margin remain separate Lean proofs.')


if __name__ == '__main__':
    main()
