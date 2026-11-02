#!/usr/bin/env python3
"""Independent Decimal short-sum Gram and prescribed-detector reconstruction.

The C kernel uses directed MPFR short sums, also checked against complete residue periods. This reference
uses the short-sum identity, rational Bernoulli coefficients and Decimal
Euler-Maclaurin digamma, then independently solves every projection.
"""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
from pathlib import Path
import json
import subprocess

getcontext().prec = 100
checks = 0


def check(ok, detail):
    global checks
    checks += 1
    assert ok, detail


def dec(x):
    x = F(x)
    return D(x.numerator)/D(x.denominator)


def bernoulli(n):
    a = [F() for _ in range(n+1)]
    result = []
    for m in range(n+1):
        a[m] = F(1, m+1)
        for j in range(m, 0, -1):
            a[j-1] = j*(a[j-1]-a[j])
        result.append(a[0])
    return result


BERNOULLI = bernoulli(80)


@lru_cache(None)
def psi(x):
    value = dec(x)
    correction = D()
    while value < 256:
        correction += 1/value
        value += 1
    return value.ln()-1/(2*value)-sum((dec(BERNOULLI[2*k])/(2*k*value**(2*k)) for k in range(1, 41)), D())-correction


@lru_cache(None)
def short(n, a):
    return sum((D((a*r) % n)*psi(F(r, n)) for r in range(1, n)), D())/n


@lru_cache(None)
def gram(j, k):
    g = gcd(j, k)
    h, t = k//g, j//g
    inner = (short(j, 1)+short(k, 1)-D(h).ln()*(j-1)/2
             -D(t).ln()*(k-1)/2+psi(F(1))+D(g).ln())/g
    return (short(h, t % h)+short(t, h % t)+psi(F(1))-inner)/(j*k//g)


def solve(matrix, rhs):
    a = [list(row)+[value] for row, value in zip(matrix, rhs)]
    n = len(a)
    # Independent full Gauss-Jordan elimination with pivoting.
    for k in range(n):
        pivot = max(range(k, n), key=lambda i: abs(a[i][k]))
        a[k], a[pivot] = a[pivot], a[k]
        q = a[k][k]
        a[k] = [v/q for v in a[k]]
        for i in range(n):
            if i == k:
                continue
            q = a[i][k]
            a[i] = [v-q*w for v, w in zip(a[i], a[k])]
    return [row[-1] for row in a]


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), D())


def reference(N):
    top = 4*N
    G = [[gram(j, k) for k in range(2, top+1)] for j in range(2, top+1)]
    means = [D(j).ln()/j for j in range(2, top+1)]
    detail_rhs = [D(2).sqrt()/(2*j) for j in range(2, top+1)]

    def project(n, rhs):
        return solve([row[:n-1] for row in G[:n-1]], rhs[:n-1])+[D()]*(top-n)

    def pair(a, b):
        return dot(a, [dot(row, b) for row in G])

    optimizer = project(N, means)
    fine = project(top, means)
    residual = 1-dot(optimizer, means)
    fine_residual = 1-dot(fine, means)
    H = 0
    while 2**H*residual < 4:
        H += 1
    probes = []
    shallow = D()
    for h in range(H):
        s = 2**h
        coefficient = sum(((1-sum((optimizer[j-2]*D(n % j)/j for j in range(2, N+1)), D()))/(n*(n+1))
                           for n in range(s, 2*s)), D())*D(2*s).sqrt()
        shallow += coefficient**2
        M = N//s
        if M < 2:
            continue
        coarse, fine_detail = project(M, detail_rhs), project(4*M, detail_rhs)
        detail = [x-y for x, y in zip(fine_detail, coarse)]
        old = [row[:M-1] for row in G[:M-1]]
        A = [solve(old, row[:M-1]) for row in G[M-1:4*M-1]]
        v = [detail_rhs[j-2]-dot(A[j-M-1], detail_rhs[:M-1]) for j in range(M+1,4*M+1)]
        m = sum((D(j).ln()*v[j-M-1]*detail[j-2] for j in range(M+1,4*M+1)),D())
        e = sum((sum((A[j-M-1][k-2]*(D(j)/k).ln()*detail_rhs[k-2] for k in range(2,M+1)),D())*detail[j-2] for j in range(M+1,4*M+1)),D())
        lift = [D()]*(top-1)
        for j in range(2, 4*M+1):
            lift[s*j-2] += D(s).sqrt()*detail[j-2]
            if s > 1:
                lift[s-2] -= D(s).sqrt()*detail[j-2]/j
        conditioner = project(N, [dot(row, lift) for row in G])
        w = [x-y for x, y in zip(lift, conditioner)]
        probes.append(dict(root_log_part=m,root_commutator_part=e,depth=h, coarse_cutoff=M, coefficients=w, response=dot(w, means),
                           conditioned_cost=pair(w, w), raw_cost=pair(detail, detail),
                           root_response=dot(detail, means)/D(s).sqrt(), terminal_pairing=pair(optimizer, lift)))
    K = [[pair(a['coefficients'], b['coefficients']) for b in probes] for a in probes]
    b = [p['response'] for p in probes]
    return dict(residual=residual, fine_residual=fine_residual, available_gain=residual-fine_residual,
                joint_capture=dot(b, solve(K, b)), gram_trace=sum((K[i][i] for i in range(len(K))), D()),
                raw_cost_sum=sum((p['raw_cost'] for p in probes), D()), shallow_energy=shallow,
                shallow_lower=residual**2/4, shallow_horizon=H, probes=probes, gram=K, optimizer=optimizer)


def contains(bounds, value, name):
    lo, hi = D(bounds['lo']), D(bounds['hi'])
    check(lo.is_finite() and hi.is_finite() and lo <= hi and hi-lo < D('1e-38'), ('interval', name))
    check(lo-D('1e-70') <= value <= hi+D('1e-70'), (name, lo, value, hi))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bin', required=True)
    binary = str(Path(parser.parse_args().bin).resolve())
    for N in [2, 3, 4, 8, 25]:
        process = subprocess.run([binary, 'native-refinement', 'detector', str(N), '--json'],
                                 text=True, capture_output=True, timeout=180, check=True)
        check(not process.stderr, process.stderr)
        actual = json.loads(process.stdout)
        expected = reference(N)
        check(actual['schema'] == 'nfield.native-detector.v1' and actual['observation_truncation'] is False, 'native norm metadata')
        check(actual['cutoff'] == N and actual['fine_cutoff'] == 4*N and actual['failures'] == 0, 'frame metadata')
        check(actual['shallow_horizon'] == expected['shallow_horizon'], 'exact shallow horizon')
        for key in ['residual', 'fine_residual', 'available_gain', 'joint_capture', 'gram_trace', 'raw_cost_sum', 'shallow_energy', 'shallow_lower']:
            contains(actual[key], expected[key], (N, key))
        check(actual['eligible_depths'] == len(expected['probes']), 'all eligible depths')
        for a, e in zip(actual['probes'], expected['probes']):
            check(a['depth'] == e['depth'] and a['coarse_cutoff'] == e['coarse_cutoff'], 'probe metadata')
            for key in ['response', 'conditioned_cost', 'raw_cost', 'root_response', 'terminal_pairing', 'root_log_part', 'root_commutator_part']:
                contains(a[key], e[key], (N, e['depth'], key))
            contains(a['single_capture'], e['response']**2/e['conditioned_cost'], ('single capture',N,e['depth']))
            for row, value in zip(a['coefficients'], e['coefficients']):
                contains(row['coefficient'], value, ('conditioned coefficients', N, row['clock']))
            if e['depth']:
                check(abs(e['terminal_pairing']) > D('1e-8'), 'terminal pairing must be retained')
        for row in actual['gram']:
            contains(row['value'], expected['gram'][row['left']][row['right']], 'full Gram')
        for row in actual['optimizer']:
            contains(row['coefficient'], expected['optimizer'][row['clock']-2], 'old optimizer')
        if N == 25:
            row=actual['probes'][1]
            displayed=dict(root_log_part='0.08229551644126888',root_commutator_part='-0.07378835806682486',terminal_pairing='0.01224730494657876',response='-0.003740146572134734',raw_cost='0.02856309767495334',conditioned_cost='0.02476758115237015',single_capture='0.000564798649290488')
            for name,value in displayed.items():
                check(abs((D(row[name]['lo'])+D(row[name]['hi']))/2-D(value))<D('1e-17'),('published N25 table',name))
            check(D(actual['joint_capture']['lo'])>19*expected['residual']**2,'published complete gain inequality')
        if N == 2:
            contains(actual['residual'], 1-D(2).ln(), 'closed two-clock residual')
    for args in [('1',), ('101',), ('2', '--json', '--json'), ('2x',), ('2', '--output', 'file.json')]:
        p = subprocess.run([binary, 'native-refinement', 'detector', *args], text=True, capture_output=True)
        check(p.returncode != 0 and not p.stdout, ('rejected detector input', args))
    print(f'PASS prescribed native detector: {checks} checks; independent short-sum Gram, complete projections, all eligible depths, terminal pairings and joint capture at N=2,3,4,8,25, including the published sign reversal.')


if __name__ == '__main__':
    main()
