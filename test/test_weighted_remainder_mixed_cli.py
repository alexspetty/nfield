#!/usr/bin/env python3
"""Reader-facing mixed readouts checked against independent exact references."""
import argparse
from fractions import Fraction as F
from math import gcd, lcm
from pathlib import Path
import re as regex
import subprocess
from test_weighted_remainder_complex import phase_reference, unit_characters, conductor, residue_order
from test_weighted_remainder_character import character_reference, generic, product, add, delta, weight, ZERO
from test_weighted_remainder_cotangent import reference as cotangent_reference, KEYS as COTANGENT_KEYS
from test_weighted_remainder_harmonic_root import root_reference, polylog_reference, kernels, tail
from test_weighted_remainder_small_amplitude import reference as small_reference

checks = cases = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def rect_keys(name):
    return [name+'_'+x for x in ('real_lower', 'real_upper', 'imag_lower', 'imag_upper')]


def main():
    global cases
    ap = argparse.ArgumentParser();ap.add_argument('--bin', required=True);args = ap.parse_args()
    binary = str(Path(args.bin).absolute())

    def run(argv, expected=None, valid=True):
        global cases
        cases += 1
        result = subprocess.run([binary, 'weighted-remainder-state', *map(str, argv)], text=True, capture_output=True)
        check((result.returncode == 0) == valid, ('CLI admission', argv, result.returncode, result.stderr))
        if not valid:
            check(not result.stdout and bool(result.stderr), ('CLI rejected output', argv))
            return result
        check(not result.stderr, ('CLI stderr', argv, result.stderr))
        check('Exact rational endpoints; finite computations and infinite proofs are separate.' in result.stdout,
              ('finite/proof boundary', argv))
        fields = {}
        for line in result.stdout.splitlines():
            if regex.match(r'^[a-z][a-z0-9_]*=', line):
                key, value = line.split('=', 1)
                check(key not in fields, ('unique CLI field', argv, key))
                fields[key] = value
        if expected is not None:
            check(fields == {k: str(v) for k, v in expected.items()}, ('literal independent CLI fields', argv, fields, expected))
        return result

    for q, a in [(1, 0), (2, 1), (17, 5), (240, 239)]:
        expected = dict(phase_denominator=q, phase_numerator=a)
        expected.update(zip(rect_keys('phase'), phase_reference(F(a, q))))
        run(['character-phase', q, a], expected)
    for q in (2, 3, 6, 8, 12, 24, 40):
        units, chars = unit_characters(q)
        den = lcm(*(residue_order(a, q) for a in units))
        expected = dict(modulus=q, character_count=len(chars), phase_denominator=den)
        result = run(['character-table', q], expected)
        wanted = {tuple(chi.get(a, F(-1)) for a in range(q)):
                  (conductor(q, chi), int(chi[q-1] == F(1, 2))) for chi in chars}
        seen = set();odd = []
        for line in result.stdout.splitlines():
            if not line.startswith('character '):
                continue
            row = list(map(int, line.split()[1:]));index, level, parity = row[:3]
            phase = tuple(F(-1) if n < 0 else F(n, den) for n in row[3:])
            check(index == len(seen) and phase not in seen and wanted.get(phase) == (level, parity),
                  ('CLI character table and induced conductor', q, row))
            seen.add(phase)
            if parity:
                odd.append((index, level, phase))
        check(seen == set(wanted), ('complete CLI unit character table', q))
        for index, level, phases in odd[:2]:
            N = 13
            expected = dict(modulus=q, character_index=index, character_conductor=level, phase_denominator=den, series_cutoff=N)
            rects = character_reference(q, phases, N)
            for name, rect in zip(('cotangent_coefficient', 'l_one_conjugate', 'l_two_prefix', 'l_two', 'mixed_product'), rects):
                expected.update(zip(rect_keys(name), rect))
            expected['l_two_norm_tail_upper'] = F(1, N)
            run(['character-l', q, index, N], expected)
    for q, N, K, M in [(2, 1, 1, 2), (6, 7, 13, 11), (24, 31, 29, 37), (240, 1, 240, 2)]:
        units, chars = generic(q);mixed = ZERO
        for chi in chars:
            mixed = add(mixed, character_reference(q, chi, N)[-1])
        d = delta(q);zl = sum((F(1, n**3) for n in range(1, K+1)), F(0));zu = zl+F(1, 2*K*K)
        dl, du = zl*d*len(units), zu*d*len(units)
        quotient = product(mixed[:2], (1/du, 1/dl));el, eu = F(1, 2)-quotient[1], F(1, 2)-quotient[0]
        al = sum((weight(n) for n in range(q, M+1, q)), F(0));au = al+1-sum((weight(n) for n in range(2, M+1)), F(0))
        expected = dict(modulus=q, series_cutoff=N, zeta_cutoff=K, period_cutoff=M, character_count=len(units),
                        odd_count=len(chars), induced_odd_count=sum(d < q for d in chars.values()))
        expected.update(zip(rect_keys('mixed_moment'), mixed))
        expected.update(delta=d, zeta_lower=zl, zeta_upper=zu, denominator_lower=dl, denominator_upper=du,
                        eta_lower=el, eta_upper=eu, positive_amplitude_lower=max(al, el), positive_amplitude_upper=min(au, eu))
        run(['mixed-moment', q, N, K, M], expected)
    for q, N, K in [(1, 1, 1), (2, 240, 1), (6, 7, 13), (40, 31, 29)]:
        expected = dict(modulus=q, series_cutoff=N, zeta_cutoff=K)
        expected.update(zip(COTANGENT_KEYS, cotangent_reference(q, N, K)))
        run(['cotangent-sums', q, N, K], expected)
    for re, im, N in [(F(0), F(0), 240), (F(3, 5), F(4, 5), 13), (F(1, 2**62), F(-1, 3), 7)]:
        values = polylog_reference(re, im, N)
        expected = dict(series_cutoff=N, binary_exponent=(2*N-1).bit_length(), z_real=re, z_imag=im, tail_upper=values[2])
        expected.update(zip(rect_keys('prefix'), values[3:7]));expected.update(zip(rect_keys('value'), values[7:11]))
        run(['harmonic-polylog', re, im, N], expected)
    root_keys = ('harmonic_tail_upper cubic_prefix_lower cubic_prefix_upper cubic_tail_upper cubic_lower cubic_upper '
                 'sine_prefix_lower sine_prefix_upper sine_tail_upper sine_lower sine_upper zeta_lower zeta_upper '
                 'angle_weight_lower angle_weight_upper identity_lower identity_upper').split()
    for q, a, N, K in [(1, 0, 240, 1), (3, 1, 13, 7), (40, 23, 31, 29), (240, 239, 1, 240)]:
        values = root_reference(q, a, N, K)
        expected = dict(phase_denominator=q, phase_numerator=a, series_cutoff=N, zeta_cutoff=K, binary_exponent=(2*N-1).bit_length())
        for name, pos in [('phase', 0), ('harmonic_prefix', 4), ('harmonic', 8)]:
            expected.update(zip(rect_keys(name), values[pos:pos+4]))
        expected.update(zip(root_keys, values[12:]));run(['harmonic-root', q, a, N, K], expected)
    for q, N in [(1, 2), (6, 13), (240, 1)]:
        average = ZERO
        for n in range(1, N+1):
            for a in range(q):
                average = add(average, tuple(kernels[n]/q*x for x in phase_reference(F(a*n % q, q))))
        selected = sum((kernels[n] for n in range(q, N+1, q)), F(0))
        expected = dict(modulus=q, series_cutoff=N, binary_exponent=(2*N-1).bit_length(), selected_prefix=selected,
                        tail_upper=tail(N), lower=selected, upper=selected+tail(N))
        expected.update(zip(rect_keys('root_average_prefix'), average));run(['harmonic-root-average', q, N], expected)
    for q, n in [(1, -17), (2, 2), (3, -1), (12, 10**100+17)]:
        r = n % q;lo = hi = F(0)
        if not r:
            rhs = F(0), F(0)
        else:
            for a in range(1, q):
                bounds = product(phase_reference(F(a*r % q, q))[2:], (F(2*a-q, 2*q),)*2)
                lo += bounds[0];hi += bounds[1]
            from test_weighted_remainder_character import cotangent
            l, u = cotangent(F(r, q));rhs = -u/2, -l/2
        run(['sine-transform', q, n], dict(modulus=q, frequency=n, lower=lo, upper=hi,
                                         cotangent_rhs_lower=rhs[0], cotangent_rhs_upper=rhs[1]))
    small_keys = ('three_prefix three_lower three_upper catalan_prefix catalan_lower catalan_upper six_prefix six_lower '
                  'six_upper induced_prefix_rhs induced_factor induced_lower induced_upper l_tail_upper zeta_lower zeta_upper '
                  'sqrt_three_lower sqrt_three_upper eta_three_lower eta_three_upper eta_four_lower eta_four_upper '
                  'eta_six_direct_lower eta_six_direct_upper eta_six_relation_lower eta_six_relation_upper').split()
    for N, K in [(1, 240), (13, 7), (240, 1)]:
        expected = dict(series_cutoff=N, zeta_cutoff=K);expected.update(zip(small_keys, small_reference(N, K)))
        run(['small-amplitudes', N, K], expected)
    invalid = [['character-phase'], ['character-phase', 0, 0], ['character-phase', 241, 0], ['character-phase', 3, 3],
               ['character-phase', '+3', 1], ['character-table', 1], ['character-table', 241],
               ['character-l', 3, 0, 1], ['character-l', 3, 3, 1], ['character-l', 3, 1, 0],
               ['mixed-moment', 1, 1, 1, 2], ['mixed-moment', 3, 1, 0, 2], ['mixed-moment', 3, 1, 1, 1],
               ['mixed-moment', 3, 241, 1, 2], ['cotangent-sums', 0, 1, 1], ['cotangent-sums', 3, 0, 1],
               ['cotangent-sums', 3, 1, 241], ['harmonic-root', 3, 3, 1, 1], ['harmonic-root', 3, 1, 0, 1],
               ['harmonic-root-average', 0, 1], ['harmonic-root-average', 3, 241],
               ['sine-transform', 0, 1], ['sine-transform', 3, '+1'], ['sine-transform', 3, '1/2'],
               ['sine-transform', 3, '-'], ['sine-transform', 3, '1'*1001], ['small-amplitudes', 0, 1],
               ['small-amplitudes', 1, 241], ['small-amplitudes', 1, 1, 1]]
    invalid += [['harmonic-polylog', value, '0', 1] for value in ('', '-', '+1', '1e-2', '0.5', 'nan',
                '1/0', '1/-2', '1//2', '1/', '1'*161, str(F(1, 2**63)), '2')]
    invalid += [['harmonic-polylog', '3/4', '3/4', 1], ['harmonic-polylog', '0', '0', 241]]
    for argv in invalid:
        run(argv, valid=False)
    help_result = subprocess.run([binary, 'help', 'weighted-remainder-state'], text=True, capture_output=True)
    check(help_result.returncode == 0, 'help command')
    for name in ['character-phase', 'character-table', 'character-l', 'mixed-moment', 'cotangent-sums',
                 'harmonic-polylog', 'harmonic-root', 'harmonic-root-average', 'sine-transform', 'small-amplitudes']:
        check('weighted-remainder-state '+name+' ' in help_result.stdout, ('documented CLI action', name))
    print(f'PASS mixed-moment CLI: {checks} checks, {cases} calculation/admission cases, ten documented actions; '
          'all rational fields compared with independent references.')


if __name__ == '__main__':
    main()
