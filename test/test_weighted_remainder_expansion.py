#!/usr/bin/env python3
"""Exact uniform-expansion checks with independent divisor and series data."""
import argparse
from fractions import Fraction as F
from math import gcd, prod
from pathlib import Path
import subprocess
from test_weighted_remainder_constants import KEYS as CONSTANT_KEYS, constant_reference_table, log_reference

KEYS = ('delta jordan_three totient_ratio rho prime_factor_plus_product '
        'log_lower log_upper nu_lower nu_upper mobius_inverse mobius_log_lower mobius_log_upper '
        'harmonic_prefix harmonic_error_raw_lower harmonic_error_raw_upper '
        'harmonic_error_lower harmonic_error_upper harmonic_error_bound '
        'seed_main_lower seed_main_upper seed_error_bound seed_lower seed_upper '
        'main_lower main_upper error_upper amplitude_lower amplitude_upper '
        'prime_power_main_lower prime_power_main_upper prime_leading_lower prime_leading_upper').split()
checks = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def product_interval(a, b):
    corners = [x*y for x in a for y in b]
    return min(corners), max(corners)


def overlap(a, b, why):
    check(a[0] <= b[1] and b[0] <= a[1], (why, a, b))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    ap.add_argument('--bin')
    args = ap.parse_args()
    constants = constant_reference_table()
    divisors = {q: [d for d in range(1, q+1) if q % d == 0] for q in range(1, 241)}
    phi = {q: sum(gcd(a, q) == 1 for a in range(q)) for q in range(1, 241)}
    mu, jordan = {}, {}
    for q in range(1, 241):
        mu[q] = (1 if q == 1 else 0)-sum(mu[d] for d in divisors[q] if d < q)
        jordan[q] = q**3-sum(jordan[d] for d in divisors[q] if d < q)
    harmonic = [F(0)]*241
    for n in range(1, 241):
        harmonic[n] = harmonic[n-1]+F(1, n)
    prime_factors = {q: [p for p in divisors[q] if p > 1 and len(divisors[p]) == 2]
                     for q in range(1, 241)}

    # The expansion algorithm does not use these period masses or harmonic
    # subseries. They supply a separate consistency check of the full values.
    R = 1024
    w, kernel = [F(0)]*(R+1), [F(0)]*(R+1)
    H, zeta = F(0), F(0)
    for n in range(1, R+1):
        kernel[n] = H/n**2
        w[n] = (n*H-sum((d**3*w[d] for d in range(1, n) if n % d == 0), F(0)))/n**3
        H += F(1, n)
        zeta += F(1, n**3)
    mass_tail = 1-sum(w, F(0))
    seed_tail = zeta+F(1, 2*R*R)-sum(kernel, F(0))
    check(mass_tail > 0 and seed_tail > 0, 'long positive reference tails')
    eta, seed = {}, {}
    for q in range(1, 241):
        a = sum(w[q::q], F(0))
        f = sum(kernel[q::q], F(0))
        eta[q] = (a, a+mass_tail)
        seed[q] = (f, f+seed_tail)
    eta[1] = (F(1), F(1))
    eta[2] = (F(1, 2), F(1, 2))
    seed[1] = (zeta, zeta+F(1, 2*R*R))

    queries = dict.fromkeys((q, N) for q in range(1, 241) for N in (1, 2, 12, 240))
    queries.update(dict.fromkeys((q, N) for q in (1, 2, 8, 30, 239, 240) for N in range(1, 241)))
    queries.update(dict.fromkeys([(0, 1), (241, 1), (1, 0), (1, 241)]))
    run = subprocess.run([str(Path(args.driver).resolve())],
                         input=''.join(f'{q} {N}\n' for q, N in queries),
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr[-3000:]))
    lines = run.stdout.splitlines()
    check(lines[0].startswith('EDGES '), lines[:1])
    edges = int(lines[0].split()[1])
    check(len(lines) == len(queries)+1, ('record count', len(lines), len(queries)))
    prime_power_cases = 0
    cli_references = {}
    for (q, N), line in zip(queries, lines[1:]):
        data = line.split()
        check(data[0] == 'R', ('operation', q, N))
        valid = 1 <= q <= 240 and 1 <= N <= 240
        check(int(data[1]) == valid, ('admission', q, N))
        if not valid:
            check(len(data) == 2, ('failed readout', q, N))
            continue
        primes = prime_factors[q]
        p, a = 0, 0
        if len(primes) == 1:
            p = primes[0]
            power = 1
            while power < q:
                power *= p
                a += 1
            check(power == q, ('independent prime power', q, p, a))
            prime_power_cases += 1
        check(list(map(int, data[2:8])) == [q, q >= 2, p, a, N, (2*N-1).bit_length()], ('metadata', q, N))
        check(len(data) == 62, ('field count', q, N, len(data)))
        out = dict(zip(KEYS, map(F, data[8:40])))
        cc = dict(zip(CONSTANT_KEYS, map(F, data[40:])))
        check(cc == constants[N], ('embedded constant readout', q, N))
        expected = {k: F(0) for k in KEYS}
        delta, ratio = F(jordan[q], q**3), F(phi[q], q)
        rho = ratio/delta
        plus = F(prod(p+1 for p in primes))
        ll, lh = log_reference(q)
        nl = sum((log_reference(p)[0]/(p-1) for p in primes), F(0))
        nh = sum((log_reference(p)[1]/(p-1) for p in primes), F(0))
        ml = sum((min(F(mu[d], d)*x for x in log_reference(d)) for d in divisors[q]), F(0))
        mh = sum((max(F(mu[d], d)*x for x in log_reference(d)) for d in divisors[q]), F(0))
        inverse = sum((F(mu[d], d) for d in divisors[q]), F(0))
        check(inverse == ratio, ('literal totient/Mobius inverse', q))
        overlap((ml, mh), (-ratio*nh, -ratio*nl), ('signed logarithmic divisor identity', q, N))
        h = harmonic[q-1]
        el, eh = h-lh-cc['gamma_upper']+F(1, 2*q), h-ll-cc['gamma_lower']+F(1, 2*q)
        eb = F(1, 12*q*q)
        zl, zh = product_interval((cc['zeta_two_lower'], cc['zeta_two_upper']),
                                  (ll+cc['kappa_lower'], lh+cc['kappa_upper']))
        sl, sh = zl/q**2-cc['zeta_three_upper']/(2*q**3), zh/q**2-cc['zeta_three_lower']/(2*q**3)
        se = cc['zeta_four_upper']/(12*q**4)
        expected.update(delta=delta, jordan_three=F(jordan[q]), totient_ratio=ratio, rho=rho,
            prime_factor_plus_product=plus, log_lower=ll, log_upper=lh, nu_lower=nl, nu_upper=nh,
            mobius_inverse=inverse, mobius_log_lower=ml, mobius_log_upper=mh,
            harmonic_prefix=h, harmonic_error_raw_lower=el, harmonic_error_raw_upper=eh,
            harmonic_error_lower=max(el, -eb), harmonic_error_upper=min(eh, F(0)), harmonic_error_bound=eb,
            seed_main_lower=sl, seed_main_upper=sh, seed_error_bound=se, seed_lower=sl-se, seed_upper=sh)
        if q >= 2:
            scale = (cc['leading_lower']*rho/q**2, cc['leading_upper']*rho/q**2)
            al, ah = product_interval(scale, (ll+cc['kappa_lower']+nl, lh+cc['kappa_upper']+nh))
            err = cc['zeta_four_upper']*plus/(12*cc['zeta_three_lower']*q**4*delta)
            expected.update(main_lower=al, main_upper=ah, error_upper=err,
                            amplitude_lower=al-err, amplitude_upper=ah+err)
            if p:
                pl, ph = log_reference(p)
                pl, ph = product_interval(scale, (a*pl+cc['kappa_lower']+pl/(p-1),
                                                  a*ph+cc['kappa_upper']+ph/(p-1)))
                expected.update(prime_power_main_lower=pl, prime_power_main_upper=ph)
                overlap((pl, ph), (al, ah), ('log prime power/main compatibility', q, N))
                overlap((pl-err, ph+err), eta[q], ('prime-power full mass reference', q, N))
                if a == 1:
                    pl, ph = product_interval((cc['leading_lower'], cc['leading_upper']), log_reference(p))
                    expected.update(prime_leading_lower=pl/q**2, prime_leading_upper=ph/q**2)
        for k in KEYS:
            check(out[k] == expected[k], ('exact independent expansion endpoint', q, N, k, out[k], expected[k]))
        check(-eb <= out['harmonic_error_lower'] <= out['harmonic_error_upper'] <= 0, ('harmonic strict-range enclosure', q, N))
        check(out['seed_lower'] <= out['seed_upper'], ('seed interval order', q, N))
        overlap((out['seed_lower'], out['seed_upper']), seed[q], ('long harmonic seed reference', q, N))
        if q >= 2:
            check(out['amplitude_lower'] <= out['amplitude_upper'], ('amplitude interval order', q, N))
            overlap((out['amplitude_lower'], out['amplitude_upper']), eta[q], ('long positive mass reference', q, N))
        # Save only independently checked fields for CLI correspondence.
        cli_references[q, N] = (expected.copy(), constants[N], p, a)
    cli_cases = 0
    if args.bin:
        binary = str(Path(args.bin).absolute())
        for op in ('harmonic-expansion', 'amplitude-expansion'):
            for q, N in ((1, 1), (1, 240), (2, 1), (2, 240), (8, 12), (30, 240), (239, 240), (240, 2)):
                if op == 'amplitude-expansion' and q == 1:
                    continue
                cli = subprocess.run([binary, 'weighted-remainder-state', op, str(q), str(N)], text=True, capture_output=True)
                check(cli.returncode == 0 and not cli.stderr, ('CLI expansion exit', op, q, N, cli.stderr))
                values = dict(line.split('=', 1) for line in cli.stdout.splitlines() if '=' in line)
                expected, cc, p, a = cli_references[q, N]
                included = set(KEYS)
                if q == 1:
                    included -= {'main_lower', 'main_upper', 'error_upper', 'amplitude_lower', 'amplitude_upper'}
                if not p:
                    included -= {'prime_power_main_lower', 'prime_power_main_upper'}
                if a != 1:
                    included -= {'prime_leading_lower', 'prime_leading_upper'}
                meta = {'conductor': q, 'amplitude_expansion_available': int(q >= 2), 'prime_base': p,
                        'prime_exponent': a, 'constant_cutoff': N, 'log_tail_binary_exponent': (2*N-1).bit_length()}
                check(set(values) == included|set(CONSTANT_KEYS)|set(meta), ('CLI field visibility', op, q, N))
                check({k: int(values[k]) for k in meta} == meta, ('CLI metadata', op, q, N))
                check({k: F(values[k]) for k in included} == {k: expected[k] for k in included}, ('independent CLI expansion', op, q, N))
                check({k: F(values[k]) for k in CONSTANT_KEYS} == cc, ('independent CLI constants', op, q, N))
                cli_cases += 1
            bad = [[], ['2'], ['0', '1'], ['241', '1'], ['2', '0'], ['2', '241'], ['2.0', '1'], ['+2', '1'],
                   ['-2', '1'], ['', '1'], ['x', '1'], ['2', '1', 'extra']]
            if op == 'amplitude-expansion':
                bad.append(['1', '1'])
            for argv in bad:
                cli = subprocess.run([binary, 'weighted-remainder-state', op, *argv], text=True, capture_output=True)
                check(cli.returncode == 1 and not cli.stdout and 'conductor' in cli.stderr, ('CLI invalid expansion', op, argv))
                cli_cases += 1
    print(f'PASS: {checks} checks; {len(queries)} API records; {edges} C edge assertions; '
          f'{prime_power_cases} prime-power cases; {cli_cases} CLI cases; all conductors and constant cutoffs through 240.')
    print('Literal totient counts, independent divisor inversion, exact logarithm references, '
          'signed Mobius sums and separate positive mass/harmonic series through 1024. '
          'Finite consistency does not prove the infinite uniform expansion or its error bound.')


if __name__ == '__main__':
    main()
