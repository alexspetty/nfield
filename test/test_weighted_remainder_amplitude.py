#!/usr/bin/env python3
"""Independent positive-pair, divisor-inverse and full-series interval checks.

Literal (a,b) pairs give both harmonic kernels and collision masses. Jordan
counts and Mobius values use proper-divisor inversion, unlike production's
prime factors. Longer positive series supply independent consistency checks;
universal containment and convergence remain separate Lean evidence.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
from pathlib import Path
import subprocess

KEYS = ('delta jordan_three zeta_lower zeta_upper zeta_tail retained_amplitude '
        'amplitude_lower amplitude_upper conductor_upper seed_prefix seed_budget_lower '
        'seed_lower seed_upper seed_tail_upper refinement_numerator_lower refinement_numerator_upper '
        'refinement_lower refinement_upper jordan_sum_lower jordan_sum_upper jordan_rhs_lower jordan_rhs_upper '
        'mobius_prefix_lower mobius_prefix_upper mobius_tail_upper mobius_lower mobius_upper prime_lower prime_upper period_tail_bound period_tail_upper').split()
checks = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


def interval_sum(terms):
    lo, hi = F(0), F(0)
    for c, a, b in terms:
        lo += min(c*a, c*b)
        hi += max(c*a, c*b)
    return lo, hi


def divide(nl, nh, dl, dh):
    check(0 < dl <= dh and nl <= nh, ('interval division domain', nl, nh, dl, dh))
    vals = [n/d for n in (nl, nh) for d in (dl, dh)]
    return min(vals), max(vals)


def overlaps(a, b, why):
    check(a[0] <= b[1] and b[0] <= a[1], (why, a, b))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    ap.add_argument('--bin')
    args = ap.parse_args()
    divisors = {n: [d for d in range(1, n+1) if n % d == 0] for n in range(1, 241)}
    jordan, mu = [0]*241, [0]*241
    for n in range(1, 241):
        jordan[n] = n**3-sum(jordan[d] for d in divisors[n] if d < n)
        mu[n] = (1 if n == 1 else 0)-sum(mu[d] for d in divisors[n] if d < n)
    triple_visits = 0
    for q in range(1, 31):
        count = 0
        for a in range(q):
            for b in range(q):
                g = gcd(gcd(a, b), q)
                count += sum(gcd(g, c) == 1 for c in range(q))
                triple_visits += q
        check(count == jordan[q], ('literal primitive triples', q, count, jordan[q]))
    pair_visits = 0
    kernel, weights = [F(0)]*241, [F(0)]*241
    for n in range(2, 241):
        for a in range(1, n):
            b = n-a
            term = F(1, 2*a*b*n)
            kernel[n] += term
            if gcd(a, b) == 1:
                weights[n] += term
            pair_visits += 1
    seed = {q: [F(0)]*241 for q in range(1, 241)}
    mass = [F(0)]*241
    zeta = [F(0)]*241
    for M in range(1, 241):
        mass[M] = mass[M-1]+weights[M]
        zeta[M] = zeta[M-1]+F(1, M**3)
        for q in range(1, 241):
            seed[q][M] = seed[q][M-1]+(kernel[M] if M % q == 0 else 0)

    # A separate, longer positive reference. Its weights use triangular
    # harmonic budgets, and its seed uses literal harmonic terms. Bounds
    # use the proved total masses; they do not certify the infinite theorem.
    R = 1024
    long_weights, long_kernel = [F(0)]*(R+1), [F(0)]*(R+1)
    H, long_zeta = F(0), F(0)
    for n in range(1, R+1):
        long_kernel[n] = H/F(n*n)
        long_weights[n] = (n*H-sum((d**3*long_weights[d] for d in range(1, n) if n % d == 0), F(0)))/n**3
        long_zeta += F(1, n**3)
        H += F(1, n)
    check(long_weights[:241] == weights, 'independent triangular/primitive-pair weights')
    check(long_kernel[:241] == kernel, 'independent harmonic/positive-pair seed')
    zref = (long_zeta, long_zeta+F(1, 2*R*R))
    mass_tail = 1-sum(long_weights, F(0))
    seed_tail = zref[1]-sum(long_kernel, F(0))
    check(mass_tail > 0 and seed_tail > 0, 'positive long reference tails')
    eta_ref, seed_ref = {}, {}
    for q in range(1, 241):
        a = sum(long_weights[q::q], F(0))
        f = sum(long_kernel[q::q], F(0))
        eta_ref[q] = (F(1), F(1)) if q == 1 else (a, a+mass_tail)
        seed_ref[q] = (f, f+seed_tail)

    @lru_cache(None)
    def base(q, M, N):
        zlo, zhi = zeta[N], zeta[N]+F(1, 2*N*N)
        al, ah, fl, fh, budgets = {}, {}, {}, {}, {}
        for d in divisors[q]:
            if d == 1:
                al[d] = ah[d] = F(1)
            else:
                b = (2*d-1).bit_length()
                al[d] = sum(weights[d:M+1:d], F(0))
                ah[d] = min(al[d]+1-mass[M], al[d]+F(2*(2*M-1).bit_length()+3, d*M), F(4*(b+1), d*d))
        for d in divisors[q]:
            bl = sum((jordan[e]*al[e] for e in divisors[d]), F(0))
            bh = sum((jordan[e]*ah[e] for e in divisors[d]), F(0))
            budgets[d] = (bl, bh)
            fl[d] = max(seed[d][M], zlo*bl/d**3)
            fh[d] = zhi*bh/d**3
        b = (2*q-1).bit_length() if q > 1 else 0
        jl, jh = budgets[q]
        delta = F(jordan[q], q**3)
        nl, nh = interval_sum((F(mu[d], d**3), fl[q//d], fh[q//d]) for d in divisors[q])
        rl, rh = divide(nl, nh, zlo*delta, zhi*delta)
        jrl, jrh = divide(q**3*fl[q], q**3*fh[q], zlo, zhi)
        prime = q >= 2 and len(divisors[q]) == 2
        if prime:
            pl, ph = interval_sum([(F(1), fl[q], fh[q]), (F(-1, q**3), fl[1], fh[1])])
            pl, ph = divide(pl, ph, zlo*delta, zhi*delta)
        else:
            pl = ph = F(0)
        ans = dict(zip(KEYS[:22], [delta, F(jordan[q]), zlo, zhi, zhi-zlo,
            mass[M] if q == 1 else al[q], al[q], ah[q], F(4*(b+1), q*q) if q > 1 else F(1),
            seed[q][M], zlo*jl/q**3, fl[q], fh[q], fh[q]-seed[q][M], nl, nh, rl, rh,
            jl, jh, jrl, jrh]))
        ans.update(prime_lower=pl, prime_upper=ph,
                   period_tail_bound=F(2*(2*M-1).bit_length()+3, q*M),
                   period_tail_upper=ah[q]-(mass[M] if q == 1 else al[q]))
        return ans, fl, fh, b, prime

    queries = {}

    def add(*q):
        queries[tuple(map(str, q))] = None

    for q in range(242):
        add('L', q);add('Z', q)
    for q in range(1, 241):
        for M in range(241):
            add('S', q, M)
        for M in (2, 12, 240):
            for N, D in ((1, 1), (2, 12), (12, 2), (240, 240)):
                add('R', q, M, N, D)
    for M in range(2, 241):
        for q in (1, 2, 6, 30, 239, 240):
            add('R', q, M, M % 240+1, 241-M)
    for q in [('S', 0, 2), ('S', 241, 2), ('S', 2, 241), ('R', 0, 2, 1, 1),
              ('R', 241, 2, 1, 1), ('R', 1, 1, 1, 1), ('R', 1, 241, 1, 1),
              ('R', 1, 2, 0, 1), ('R', 1, 2, 241, 1), ('R', 1, 2, 1, 0), ('R', 1, 2, 1, 241)]:
        add(*q)
    run = subprocess.run([str(Path(args.driver).resolve())], input=''.join(' '.join(q)+'\n' for q in queries),
                         text=True, capture_output=True)
    check(run.returncode == 0, (run.returncode, run.stderr[-3000:]))
    lines = run.stdout.splitlines()
    check(lines[0].startswith('EDGES '), lines[:1])
    edges = int(lines[0].split()[1])
    check(len(lines) == len(queries)+1, ('record count', len(lines), len(queries)))
    results, refinements = {}, 0
    for query, line in zip(queries, lines[1:]):
        p = line.split();op = query[0];vals = list(map(int, query[1:]))
        check(p[0] == op, ('query operation', query, p[:2]))
        if op in ('L', 'Z'):
            valid = 1 <= vals[0] <= 240
        elif op == 'S':
            valid = 1 <= vals[0] <= 240 and 0 <= vals[1] <= 240
        else:
            valid = 1 <= vals[0] <= 240 and 2 <= vals[1] <= 240 and 1 <= vals[2] <= 240 and 1 <= vals[3] <= 240
        check(int(p[1]) == valid, ('admission', query, p[:2]))
        if not valid:
            check(len(p) == 2, ('failure readout', query));continue
        data = p[2:]
        if op == 'L':
            q = vals[0]
            check(list(map(F, data)) == [F(jordan[q], q**3), F(jordan[q])], ('independent Jordan factors', q))
        elif op == 'Z':
            N = vals[0];expected = (zeta[N], zeta[N]+F(1, 2*N*N))
            check(tuple(map(F, data)) == expected, ('cubic prefix and tail', N))
            overlaps(expected, zref, ('long cubic reference', N))
        elif op == 'S':
            q, M = vals
            check(list(map(F, data)) == [seed[q][M]], ('literal positive-pair prefix', q, M))
        else:
            q, M, N, D = vals;expected, fl, fh, b, prime = base(q, M, N);expected = dict(expected)
            check(list(map(int, data[:7])) == [q, M, N, D, b, prime, (2*M-1).bit_length()], ('metadata', query))
            check(len(data) == 38, ('field count', query))
            actual = dict(zip(KEYS, map(F, data[7:])))
            ml, mh = interval_sum((F(mu[d], d**3), fl[q//gcd(q, d)], fh[q//gcd(q, d)]) for d in range(1, D+1))
            err = (zeta[N]+F(1, 2*N*N))*F(1, 2*D*D)
            expected.update(mobius_prefix_lower=ml, mobius_prefix_upper=mh, mobius_tail_upper=err,
                            mobius_lower=ml-err, mobius_upper=mh+err)
            for k in KEYS:
                check(actual[k] == expected[k], ('exact pair/divisor reference', query, k, actual[k], expected[k]))
            for prefix in ('amplitude', 'refinement', 'mobius'):
                lo, hi = actual[prefix+'_lower'], actual[prefix+'_upper']
                check(lo <= hi, ('ordered full interval', query, prefix))
                overlaps((lo, hi), eta_ref[q], ('long positive mass reference', query, prefix))
                if q in (1, 2):
                    check(lo <= F(1, q) <= hi, ('known full amplitude', query, prefix))
            retained = actual['retained_amplitude']
            check(F(0) <= actual['period_tail_upper'] <= actual['period_tail_bound'], ('period tail bound ordering', query))
            long_omitted = sum(long_weights[q*((M//q)+1)::q], F(0))
            check(long_omitted <= actual['period_tail_upper'], ('later literal omitted masses', query))
            check(retained+actual['period_tail_upper'] == actual['amplitude_upper'], ('tail/whole amplitude relation', query))
            overlaps((actual['seed_lower'], actual['seed_upper']), seed_ref[q], ('long harmonic reference', query))
            if q == 1:
                overlaps((actual['seed_lower'], actual['seed_upper']), zref, ('F(1)=zeta(3)', query))
            if q == 2:
                overlaps((actual['seed_lower'], actual['seed_upper']), tuple(F(9, 16)*z for z in zref), ('F(2)=9*zeta(3)/16', query))
            overlaps((actual['jordan_sum_lower'], actual['jordan_sum_upper']),
                     (actual['jordan_rhs_lower'], actual['jordan_rhs_upper']), ('full Jordan budget', query))
            if prime:
                check((actual['prime_lower'], actual['prime_upper']) == (actual['refinement_lower'], actual['refinement_upper']), ('literal prime refinement retains F1', query))
            results[query] = actual;refinements += 1
    cli_count = 0
    if args.bin:
        binary = str(Path(args.bin).resolve())
        for q in (1, 2, 3, 4, 6, 12, 30, 120, 239, 240):
            for M, N, D in ((2, 1, 1), (12, 2, 12), (240, 240, 240)):
                query = tuple(map(str, ('R', q, M, N, D)))
                r = subprocess.run([binary, 'weighted-remainder-state', 'amplitude-refinement', *query[1:]], text=True, capture_output=True)
                check(r.returncode == 0, ('CLI success', query, r.stderr))
                data = dict(line.split('=', 1) for line in r.stdout.splitlines() if '=' in line)
                check([int(data[k]) for k in ['conductor', 'period_cutoff', 'zeta_cutoff', 'mobius_cutoff']] == [q, M, N, D], query)
                for k, value in results[query].items():
                    check(F(data[k]) == value, ('CLI rational endpoint', query, k))
                cli_count += 1
        for tail in [[], ['1', '2', '1'], ['0', '2', '1', '1'], ['241', '2', '1', '1'],
                     ['1', '1', '1', '1'], ['1', '241', '1', '1'], ['1', '2', '0', '1'],
                     ['1', '2', '241', '1'], ['1', '2', '1', '0'], ['1', '2', '1', '241'],
                     ['1/2', '2', '1', '1'], ['-1', '2', '1', '1'], ['1', '2', '1', '1', 'extra']]:
            r = subprocess.run([binary, 'weighted-remainder-state', 'amplitude-refinement', *tail], text=True, capture_output=True)
            check(r.returncode != 0 and 'amplitude-refinement requires' in r.stderr, ('CLI rejection', tail, r.stdout, r.stderr))
            cli_count += 1
    print(f'PASS: {checks} checks; {len(queries)} API records; {edges} C edge assertions; '
          f'{pair_visits} literal positive-pair visits; {triple_visits} primitive-triple visits; '
          f'{refinements} full refinement cases; {cli_count} CLI cases.')
    print('Exact rational references: positive pair kernels, coprime masses, independent divisor inversions, '
          'and longer positive series through 1024. All infinite containments are separate Lean proofs.')


if __name__ == '__main__':
    main()
