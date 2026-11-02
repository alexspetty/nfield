#!/usr/bin/env python3
"""Exact arithmetic and independent defining-sum checks for maximal alignment.

Production weights use reduced residues; this reference uses Mobius inversion.
Local factors come from finite defining sums and a separate loss formula.
The original triangular gcd sum supplies exact full-reset checks. A longer
Decimal Mobius sieve checks alignment against its actual positive series.
These finite checks do not certify any asymptotic or infinite theorem.
"""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm, prod
from pathlib import Path
import random
import subprocess
from test_weighted_remainder_constants import constant_reference_table, log_reference, KEYS as CONSTANT_KEYS
from test_weighted_remainder_alignment_local import reference_table

getcontext().prec = 80
KEYS = '''log_modulus_lower log_modulus_upper reset_product reset_log_lower reset_log_upper
alignment_factor_correction alignment_product_lower alignment_product_upper
alignment_log_correction_lower alignment_log_correction_upper base_log_prefix_lower base_log_prefix_upper
base_log_tail_upper alignment_log_lower alignment_log_upper reset_prefix alignment_prefix retained_mass finite_g
exact_reset triangular_sum error_bound_prefix error_tail_upper reset_main_lower reset_main_upper
alignment_main_lower alignment_main_upper reset_error_prefix_lower reset_error_prefix_upper
alignment_error_prefix_lower alignment_error_prefix_upper reset_raw_lower reset_raw_upper alignment_raw_lower alignment_raw_upper
reset_refined_lower reset_refined_upper alignment_refined_lower alignment_refined_upper reset_lower reset_upper
alignment_lower alignment_upper full_g_lower full_g_upper limiting_factor_product reset_factor_loss_sum
alignment_factor_loss_sum reset_log_loss_lower reset_log_loss_upper alignment_log_loss_lower alignment_log_loss_upper'''.split()
LOCAL_KEYS = '''coefficient main_lower main_upper error_lower error_upper error_bound log_lower log_upper
nu_lower nu_upper gamma_lower gamma_upper totient_ratio mobius_sum'''.split()
PRIMES = [n for n in range(2, 241) if sum(gcd(a, n) == 1 for a in range(1, n)) == n-1]
CONSTANTS = constant_reference_table()
checks = 0


def check(condition, detail):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(detail)


def dec(x):
    x = F(x)
    return D(x.numerator)/D(x.denominator)


def factors(n):
    result = {}
    for p in PRIMES:
        while n and n % p == 0:
            n //= p
            result[p] = result.get(p, 0)+1
    return result, n


@lru_cache(None)
def mu(n):
    if n == 1:
        return 1
    return -sum(mu(d) for d in range(1, n) if n % d == 0)


@lru_cache(None)
def harmonic(n):
    return sum((F(1, j) for j in range(1, n+1)), F())


@lru_cache(None)
def weight(k):
    return sum((F(mu(d), k*k*d)*harmonic(k//d-1) for d in range(1, k+1) if k % d == 0), F())


def interval_product(a, b):
    values = [x*y for x in a for y in b]
    return min(values), max(values)


def interval_scale(a, c):
    return tuple(sorted(x*c for x in a))


@lru_cache(None)
def local_reference(k, N):
    c = CONSTANTS[N]
    primes, rest = factors(k)
    assert rest == 1
    ll, lu = log_reference(k)
    nu = [sum((log_reference(p)[i]/(p-1) for p in primes), F()) for i in (0, 1)]
    phi = sum(gcd(j, k) == 1 for j in range(1, k))
    ratio, a = F(phi, k*k), k*weight(k)
    main = [ratio*(log+gamma+mark) for log, gamma, mark in
            zip((ll, lu), (c['gamma_lower'], c['gamma_upper']), nu)]
    bound = sum((F(d, 12*k**3) for d in range(1, k+1) if k % d == 0), F())
    return dict(zip(LOCAL_KEYS, [a, *main, a-main[1], a-main[0], bound, ll, lu, *nu,
                c['gamma_lower'], c['gamma_upper'], ratio, sum(mu(d) for d in range(1, k+1) if k % d == 0)]))


@lru_cache(None)
def triangular(n):
    return sum((F(gcd(j, n)**2, j*n) for j in range(1, n+1)), F())


def reference(n, M, N, P):
    f, _ = factors(n)
    local = {p: reference_table(p)[v][0] for p, v in f.items()}
    r = dict.fromkeys(KEYS, F())
    c = CONSTANTS[N]
    for i, side in enumerate(('lower', 'upper')):
        r['log_modulus_'+side] = sum((v*log_reference(p)[i] for p, v in f.items()), F())
        r['reset_log_'+side] = sum((a['reset_average']*log_reference(p)[i] for p, a in local.items()), F())
        r['alignment_log_correction_'+side] = sum((interval_scale(log_reference(p), a['alignment_average']-a['absent_average'])[i]
                                                  for p, a in local.items()), F())
        r['base_log_prefix_'+side] = sum((log_reference(p)[i]/(p*p-1) for p in PRIMES if p <= P), F())
        r['alignment_log_'+side] = r['base_log_prefix_'+side]+r['alignment_log_correction_'+side]
        for kind in ('reset', 'alignment'):
            r[kind+'_log_loss_'+side] = sum((interval_scale(log_reference(p), a[kind+'_average_loss'])[i]
                                            for p, a in local.items()), F())
    r['base_log_tail_upper'] = (4*log_reference(P)[1]+6)/P
    r['alignment_log_upper'] += r['base_log_tail_upper']
    r['reset_product'] = prod((a['reset_factor'] for a in local.values()), start=F(1))
    r['alignment_factor_correction'] = prod((a['alignment_factor']/a['absent_factor'] for a in local.values()), start=F(1))
    r['limiting_factor_product'] = prod((a['limiting_factor'] for a in local.values()), start=F(1))
    for kind in ('reset', 'alignment'):
        r[kind+'_factor_loss_sum'] = sum((a[kind+'_factor_relative_loss'] for a in local.values()), F())
    for side in ('lower', 'upper'):
        r['alignment_product_'+side] = c['leading_'+side]*r['alignment_factor_correction']
    r['reset_prefix'] = sum((k*weight(k) for k in range(2, M+1) if n % k == 0), F())
    r['alignment_prefix'] = sum((weight(k)*(gcd(k, n)-1)/3 for k in range(2, M+1)), F())
    r['retained_mass'] = sum((weight(k) for k in range(2, M+1)), F())
    r['finite_g'] = F(2, 3)*(r['retained_mass']-r['reset_prefix'])
    r['exact_reset'] = r['reset_prefix'] if n <= M else F()
    r['triangular_sum'] = triangular(n) if n <= 240 else F()
    locals_ = {k: local_reference(k, N) for k in range(2, M+1)}
    r['error_bound_prefix'] = F(1, 12)+sum((h['error_bound'] for h in locals_.values()), F())
    bound = c['zeta_two_upper']*c['zeta_three_upper']/12
    r['error_tail_upper'] = bound-r['error_bound_prefix']
    for side in ('lower', 'upper'):
        r['reset_error_prefix_'+side] = sum((h['error_'+side] for k, h in locals_.items() if n % k == 0), F())
        r['alignment_error_prefix_'+side] = sum((h['error_'+side]*F(gcd(k, n), k) for k, h in locals_.items()), F())
    for kind in ('reset', 'alignment'):
        products = (r['reset_product'],)*2 if kind == 'reset' else (r['alignment_product_lower'], r['alignment_product_upper'])
        main = interval_product(products, (c['gamma_lower']+r[kind+'_log_lower'], c['gamma_upper']+r[kind+'_log_upper']))
        for i, side in enumerate(('lower', 'upper')):
            sign = 2*i-1
            gamma = c['gamma_upper' if i == 0 else 'gamma_lower']
            r[kind+'_main_'+side] = main[i]-gamma
            r[kind+'_raw_'+side] = main[i]-gamma+sign*bound
            r[kind+'_refined_'+side] = main[i]-gamma+r[kind+'_error_prefix_'+side]+sign*r['error_tail_upper']
            if kind == 'alignment':
                r[kind+'_raw_'+side] = (r[kind+'_raw_'+side]-1)/3
                r[kind+'_refined_'+side] = (r[kind+'_refined_'+side]-1)/3
        r[kind+'_lower'] = max(r[kind+'_prefix'], r[kind+'_raw_lower'], r[kind+'_refined_lower'])
        r[kind+'_upper'] = min(r[kind+'_raw_upper'], r[kind+'_refined_upper'])
    if n <= M:
        r['reset_lower'] = r['reset_upper'] = r['exact_reset']
    if n == 1:
        r['alignment_lower'] = r['alignment_upper'] = F()
    r['full_g_lower'], r['full_g_upper'] = F(2, 3)*(1-r['reset_upper']), F(2, 3)*(1-r['reset_lower'])
    return r


def long_series_references():
    # The Mobius sieve avoids using the C coprime-residue weight loop.
    # Decimal rounding is covered by a separate generous 10^-60 margin.
    R = 32768
    mobius = [0]*(R+1)
    mobius[1] = 1
    for d in range(1, R+1):
        for k in range(2*d, R+1, d):
            mobius[k] -= mobius[d]
    h = [D(0)]*(R+1)
    for k in range(1, R+1):
        h[k] = h[k-1]+D(1)/k
    w = [D(0)]*(R+1)
    for d in range(1, R+1):
        if mobius[d]:
            for k in range(d, R+1, d):
                w[k] += D(mobius[d])*h[k//d-1]/(D(d)*k*k)
    result = {}
    for n in range(1, 13):
        low = sum((w[k]*(gcd(k, n)-1)/3 for k in range(2, R+1)), D(0))
        # w_k <= (1+log k)/k^2 and gcd(k,n)-1<=n-1.
        tail = D(n-1)*(2*D(R).ln()+3)/(3*R)
        result[n] = (low-D('1e-60'), low+tail+D('1e-60'))
    return result


def main():
    ap = argparse.ArgumentParser();ap.add_argument('--driver', required=True);args = ap.parse_args()
    queries = [('L', m) for m in range(242)]
    queries += [('H', k, N) for k in range(2, 241) for N in (1, 240)]
    queries += [('H', k, N) for k, N in [(0, 1), (1, 1), (241, 1), (2, 0), (2, 241)]]
    queries += [('A', n, 240, 17, 31) for n in range(1, 241)]
    queries += [('A', n, 2, 1, 240) for n in range(1, 25)]
    queries += [('A', n, 240, 240, 240) for n in range(1, 13)]
    period = 1
    for m in range(1, 241):
        period = lcm(period, m)
        queries.append(('A', period, 2+(17*m)%239, 1+(29*m)%240, 1+(31*m)%240))
    queries += [('A', p**v, 17, 13, 43) for p in PRIMES for v in (1, 7, 240)]
    rng = random.Random(20260914)
    for _ in range(24):
        n = prod(p**rng.randrange(1, 241) for p in rng.sample(PRIMES, 3))
        queries.append(('A', n, rng.randrange(2, 241), rng.randrange(1, 241), rng.randrange(1, 241)))
    queries += [('A', n, M, N, P) for n, M, N, P in [
        (0, 2, 1, 1), (-1, 2, 1, 1), (241, 2, 1, 1), (2*257, 2, 1, 1),
        (2**241, 2, 1, 1), (2**4096, 2, 1, 1), (1, 1, 1, 1), (1, 241, 1, 1),
        (1, 2, 0, 1), (1, 2, 241, 1), (1, 2, 1, 0), (1, 2, 1, 241)]]
    run = subprocess.run([str(Path(args.driver).absolute())],
        input=''.join(' '.join(map(str, q))+'\n' for q in queries), text=True, capture_output=True, timeout=300)
    check(run.returncode == 0 and not run.stderr, ('driver', run.returncode, run.stderr))
    lines = run.stdout.splitlines();check(lines[0] == 'EDGES 4892', ('edge assertions', lines[:1]))
    check(len(lines) == len(queries)+1, ('record count', len(lines), len(queries)))
    accepted = rejected = 0
    long_refs = long_series_references()
    for q, line in zip(queries, lines[1:]):
        parts = line.split();check(parts[0] == q[0], ('operation', q))
        if q[0] == 'L':
            valid = 1 <= q[1] <= 240
        elif q[0] == 'H':
            valid = 2 <= q[1] <= 240 and 1 <= q[2] <= 240
        else:
            _, n, M, N, P = q
            f, rest = factors(n) if n > 0 else ({}, n)
            valid = n > 0 and n.bit_length() <= 4096 and rest == 1 and all(v <= 240 for v in f.values()) and 2 <= M <= 240 and 1 <= N <= 240 and 1 <= P <= 240
        check(int(parts[1]) == valid, ('admission', q))
        if not valid:
            rejected += 1;check(len(parts) == 2, ('rejected output', q));continue
        accepted += 1
        if q[0] == 'L':
            check(parts[2:] == [str(lcm(*range(1, q[1]+1)))], ('exact GMP LCM', q));continue
        if q[0] == 'H':
            k, N = q[1:];check(parts[2:4] == [str(k), str(N)], ('local metadata', q))
            expected, tokens = local_reference(k, N), parts[4:]
        else:
            check(list(map(int, parts[2:9])) == [n, M, N, P, len(f), int(n <= M), int(n <= 240)], ('metadata', q))
            check(list(map(int, parts[9:250])) == [f.get(p, 0) for p in range(241)], ('complete valuation array', q))
            expected, tokens = reference(n, M, N, P), parts[250:250+len(KEYS)]
            constants = parts[250+len(KEYS):]
            check(constants == [str(CONSTANTS[N][key]) for key in CONSTANT_KEYS], ('nested constants', q))
        check(len(tokens) == len(expected), ('field count', q))
        for token, (name, value) in zip(tokens, expected.items()):
            check(F(token) == value, ('exact independent field', q, name, token, str(value)))
            check(token == str(F(token)), ('canonical rational', q, name, token))
        if q[0] == 'H':
            r = expected
            check(r['mobius_sum'] == 0 and r['error_lower'] <= r['error_upper'], ('local cancellation', q))
            # An independent gamma bracket at a longer harmonic index.
            R = 4096
            gl = dec(harmonic(R-1))-D(R).ln()+D(1)/(2*R)
            gh = gl+D(1)/(12*R*R)
            nu = sum((D(p).ln()/(p-1) for p in factors(k)[0]), D(0))
            al = dec(r['totient_ratio'])*(D(k).ln()+gl+nu)
            ah = dec(r['totient_ratio'])*(D(k).ln()+gh+nu)
            check(dec(r['main_lower']) <= al <= ah <= dec(r['main_upper']), ('independent harmonic main', q))
            check(-dec(r['error_bound']) <= dec(r['coefficient'])-ah <= dec(r['coefficient'])-al <= dec(r['error_bound']), ('actual harmonic remainder', q))
        else:
            r = expected
            check(r['error_tail_upper'] >= 0, ('positive remaining error', q))
            for kind in ('reset', 'alignment'):
                check(r[kind+'_lower'] <= r[kind+'_upper'], ('nonempty enclosure', q, kind))
            if n <= 240:
                actual = triangular(n)-1
                for variant in ('raw_', 'refined_', ''):
                    check(r['reset_'+variant+'lower'] <= actual <= r['reset_'+variant+'upper'], ('independent full gcd reset', q, variant))
                actual_g = F(2, 3)*(1-actual)
                check(r['full_g_lower'] <= actual_g <= r['full_g_upper'], ('full g uses unit mass', q))
            if n in long_refs and n > 1:
                lo, hi = long_refs[n]
                check(dec(r['alignment_lower']) <= lo <= hi <= dec(r['alignment_upper']), ('independent full alignment series bracket', q))
    print(f'PASS maximal alignment API: {checks} independent reference checks; {accepted} admitted, {rejected} rejected queries; 4892 C preservation/admission assertions. Exact LCMs, all local periods, prime towers, GMP moduli, complete field/valuation checks, triangular resets and separate long alignment series brackets. No asymptotic claim.')


if __name__ == '__main__':
    main()
