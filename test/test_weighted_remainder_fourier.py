#!/usr/bin/env python3
"""Independent finite Fourier oracle; exact rational and high precision checks.

The universal transcendental containment is proved in Lean. This oracle
also evaluates full-angle sine/cosine with a separate Machin pi calculation,
checks exact outward-grid endpoints against an expanded rational polynomial,
and transforms the actual complete conductor rows and finite age cycles.
Floating DFT comparisons do not certify an infinite theorem.
"""
import argparse
from decimal import Decimal, getcontext
from fractions import Fraction as F
from functools import lru_cache
import math
from pathlib import Path
import subprocess

getcontext().prec = 100
TKEYS = 'sin_lower sin_upper cos_lower cos_upper cot_lower cot_upper csc_squared_lower csc_squared_upper'.split()
FKEYS = 'amplitude_lower amplitude_upper g_lower g_upper y_real_lower y_real_upper y_imag_lower y_imag_upper g_mass_lower g_mass_upper y_mass_lower y_mass_upper'.split() + TKEYS
checks = 0
maximum_dft_error = 0.0


def check(value, detail):
    global checks
    checks += 1
    if not value:
        raise AssertionError(detail)


def dec(x):
    x = F(x)
    return Decimal(x.numerator) / Decimal(x.denominator)


def atan_inverse(n):
    x = Decimal(1) / n
    return sum(((-1 if j % 2 else 1) * x**(2*j+1) / (2*j+1)
                for j in range(150)), Decimal(0))


PI = 16*atan_inverse(5) - 4*atan_inverse(239)


@lru_cache(None)
def trig_reference(ratio):
    if ratio == F(1, 2):
        return Decimal(1), Decimal(0)
    x = PI*dec(ratio)
    st, ct = x, Decimal(1)
    sine, cosine = st, ct
    for j in range(1, 100):
        st *= -x*x / ((2*j)*(2*j+1))
        ct *= -x*x / ((2*j-1)*(2*j))
        sine += st
        cosine += ct
    return sine, cosine


def exact_grid_reference(q, a):
    if 2*a == q:
        return (F(1), F(1), F(0), F(0))
    x = F(3141592653589793238465, 10**21)*F(a, 4*q)
    # Direct even/odd power sums, followed by the expanded fourth power.
    re = sum(((-1)**j*x**(2*j)/math.factorial(2*j) for j in range(12)), F(0))
    im = sum(((-1)**j*x**(2*j+1)/math.factorial(2*j+1) for j in range(12)), F(0))
    cosine = re**4 - 6*re**2*im**2 + im**4
    sine = 4*re*im*(re**2-im**2)
    error = F(25, 24*math.factorial(24))
    error = (2+error)*error
    error = (2+error)*error + F(1, 2*10**20)
    grid = 10**18
    return tuple(F(math.floor((x-error)*grid), grid) if lower else
                 F(math.ceil((x+error)*grid), grid)
                 for x in (sine, cosine) for lower in (True, False))


def collision_weights(M):
    # Triangular harmonic budgets, inverted by proper-divisor subtraction.
    weights = [F(0)]*(M+1)
    harmonic = F(0)
    for k in range(2, M+1):
        harmonic += F(1, k-1)
        weights[k] = (k*harmonic-sum((d**3*weights[d] for d in range(2, k)
                                    if k % d == 0), F(0)))/k**3
    return weights


@lru_cache(None)
def profile(M, kind):
    if kind == 1:
        return tuple(collision_weights(M))
    return tuple(F(0) if k < 2 else
                 F((-1)**k, k+1) if kind == 2 else
                 F(k == M) if kind == 3 else
                 F(-7 if k == 3 else 2, 11) if kind == 4 and k in (2, 3, 5) else F(0)
                 for k in range(M+1))


def product_interval(al, ah, bl, bh):
    corners = [x*y for x in (al, ah) for y in (bl, bh)]
    return min(corners), max(corners)


def coefficient_reference(lo, hi, t):
    il, ih = product_interval(lo, hi, t['cot_lower'], t['cot_upper'])
    sl, sh = min(lo*lo, hi*hi), max(lo*lo, hi*hi)
    if lo <= 0 <= hi:
        sl = F(0)
    return dict(zip(FKEYS[:12], [lo, hi, -2*hi/3, -2*lo/3, -hi/3, -lo/3,
        il/3, ih/3, 4*sl/9, 4*sh/9, sl*t['csc_squared_lower']/9,
        sh*t['csc_squared_upper']/9]))


def near(actual, expected, detail):
    global maximum_dft_error
    error = abs(actual-expected)/max(1, abs(actual), abs(expected))
    maximum_dft_error = max(maximum_dft_error, error)
    check(error <= 5e-11, (detail, actual, expected, error))


def dft(values, q, a):
    L = len(values)
    # Full common period, original negative-exponential convention.
    # Reduce the integer phase exactly before floating evaluation. In the
    # 57360-point common cycle this avoids large-angle argument-reduction
    # error without changing the DFT, its normalization or its tolerance.
    return complex(math.fsum(float(x)*math.cos(2*math.pi*((a*n) % q)/q) for n, x in enumerate(values)),
                   -math.fsum(float(x)*math.sin(2*math.pi*((a*n) % q)/q) for n, x in enumerate(values)))/L


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    ap.add_argument('--bin')
    args = ap.parse_args()
    queries = {}

    def add(*query):
        queries[tuple(map(str, query))] = None

    for q in range(2, 241):
        add('V', q)
        for a in range(1, q):
            add('T', q, a)
            if math.gcd(a, q) == 1:
                add('R', q, q, a)
                add('R', q % 239 + 2, q, a)  # another row conductor, including wraparound
        for M in (2, 12, 120, 240):
            for full in (0, 1):
                add('C', M, q, -1, full)
        for lo, hi in [('-5', '-2'), ('-1', '3'), ('0', '0'), ('2/3', '7/2'), ('-1/99991', '-1/99991')]:
            for a in (1, -1):
                add('I', q, a, lo, hi)
    finite_cycle_cases = []
    for M in (2, 3, 4, 6, 8, 12, 30, 120, 239, 240):
        for kind in range(5):
            qs = set(range(2, M+2)) if M <= 8 else {2, 3, 4, 6, 7, M, min(240, M+1), 239}
            for q in sorted(qs):
                for a in range(1, q) if M <= 8 else (1, q-1):
                    if math.gcd(a, q) != 1:
                        continue
                    add('F', M, q, a, kind)
                    if M <= 8 or (M == 240 and kind == 3 and q in (239, 240)):
                        finite_cycle_cases.append(('F', str(M), str(q), str(a), str(kind)))
    for q in (2, 3, 6, 8, 12, 60, 120, 239, 240):
        for a in (-10**90-1, 10**100+7, -q, 0, q+1):
            add('T', q, a)
            add('C', 12, q, a, 1)
    for query in [('T', 0, 1), ('T', 1, 1), ('T', 241, 1),
                  ('C', 1, 2, 1, 1), ('C', 241, 2, 1, 1), ('C', 2, 6, 2, 1),
                  ('C', 2, 2, 1, 2), ('F', 1, 2, 1, 0), ('R', 1, 2, 1), ('R', 2, 6, 2),
                  ('I', 2, 1, 4, 3), ('I', 43, -1, '-100000000000000000000000000000000000000000000000000', '1/99999999999999999999999999')]:
        add(*query)
    proc = subprocess.run([str(Path(args.driver).resolve())], input=''.join(' '.join(q)+'\n' for q in queries),
                          capture_output=True, text=True)
    check(proc.returncode == 0, (proc.returncode, proc.stderr[-4000:]))
    lines = proc.stdout.splitlines()
    check(lines[0].startswith('EDGES '), lines[:1])
    edge_count = int(lines[0].split()[1])
    check(len(lines) == len(queries)+1, ('record count', len(lines), len(queries)))
    rows, trig, results = {}, {}, {}
    for query, line in zip(queries, lines[1:]):
        words = line.split();op = query[0]
        check(words[0] == op, (query, words[:2]))
        ok = int(words[1]);data = words[2:]
        if op in ('T', 'I'):
            q, a = map(int, query[1:3]);M = None
        elif op in ('C', 'F', 'R'):
            M, q, a = map(int, query[1:4])
        else:
            q = int(query[1]);a = 1;M = None
        valid = 2 <= q <= 240 and a % q != 0
        if op in ('C', 'F', 'R'):
            valid &= 2 <= M <= 240 and math.gcd(a, q) == 1
        if op == 'C':
            valid &= int(query[4]) in (0, 1)
        if op == 'I':
            valid &= math.gcd(a, q) == 1 and F(query[3]) <= F(query[4])
        check(ok == valid, ('domain', query, ok))
        if not ok:
            check(not data, ('failed output', query));continue
        if op == 'V':
            vals = list(map(F, data));check(len(vals) == 3*q, query)
            rows[q] = (vals[::3], vals[1::3], vals[2::3]);continue
        if op == 'R':
            results[query] = list(map(F, data));continue
        if op == 'T':
            check(list(map(int, data[:2])) == [q, a % q], query)
            record = dict(zip(TKEYS, map(F, data[2:])))
            trig[(q, a)] = record
        else:
            mode = (2 if int(query[4]) else 1) if op == 'C' else 1 if op == 'F' else 0
            check(list(map(int, data[:4])) == [mode, M if M is not None else 0, q, a % q], query)
            record = dict(zip(FKEYS, map(F, data[4:])))
        results[query] = record
    for (q, a), t in trig.items():
        sine, cosine = trig_reference(F(a % q, q))
        for name, value in [('sin', sine), ('cos', cosine), ('cot', cosine/sine), ('csc_squared', 1/(sine*sine))]:
            check(dec(t[name+'_lower']) <= value <= dec(t[name+'_upper']), ('Machin/full-angle oracle', q, a, name))
        for name in ('sin', 'cos'):
            lo, hi = t[name+'_lower'], t[name+'_upper']
            check((lo*10**18).denominator == (hi*10**18).denominator == 1, ('grid', q, a, name))
            check(F(0) <= hi-lo <= F(2, 10**18), ('width', q, a, name))
        check(t['sin_lower'] > 0, ('positive sine', q, a))
        cl, ch = product_interval(t['cos_lower'], t['cos_upper'], 1/t['sin_upper'], 1/t['sin_lower'])
        check((t['cot_lower'], t['cot_upper']) == (cl, ch), ('cot corners', q, a))
        check((t['csc_squared_lower'], t['csc_squared_upper']) == (1/t['sin_upper']**2, 1/t['sin_lower']**2), ('csc', q, a))
        if a in (1, q-1) or q <= 12:
            check(tuple(t[k] for k in TKEYS[:4]) == exact_grid_reference(q, a % q), ('independent exact polynomial', q, a))
    for query, r in results.items():
        op = query[0]
        if op in ('T', 'R'):
            continue
        if op == 'I':
            q, a = map(int, query[1:3]);lo, hi = map(F, query[3:5])
        else:
            M, q, a, kind = map(int, query[1:5])
            v = profile(M, kind if op == 'F' else 1)
            lo = sum(v[q::q], F(0))
            hi = lo + (1-sum(v, F(0)) if op == 'C' and kind else 0)
        t = trig[(q, a % q)]
        for k in TKEYS:
            check(r[k] == t[k], ('kernel reuse', query, k))
        expected = coefficient_reference(lo, hi, t)
        for k, value in expected.items():
            check(r[k] == value, ('coefficient', query, k, r[k], value))
    for q, (p, odd, c) in rows.items():
        check(sum(p) == sum(odd) == sum(c) == 0, ('row means', q))
        pl, ph, rl, rh = F(0), F(0), F(0), F(0)
        for a in range(1, q):
            if math.gcd(a, q) == 1:
                t = trig[(q, a)]
                r = results[('R', str(q), str(q), str(a))]
                check(r == [F(-1, 2), t['cot_lower']/2, t['cot_upper']/2, F(1)], ('own row coefficient', q, a))
                other = q % 239 + 2
                check(results[('R', str(other), str(q), str(a))] == [F(0)]*4, ('different conductor', q, a))
                expected = complex(-0.5, float((t['cot_lower']+t['cot_upper'])/4))
                pl += t['csc_squared_lower']/4;ph += t['csc_squared_upper']/4
                rl += t['csc_squared_lower']/4-F(1, 4);rh += t['csc_squared_upper']/4-F(1, 4)
                expected_c = 1
            else:
                expected = 0j;expected_c = 0
            near(dft(p, q, a), expected, ('actual P DFT', q, a))
            near(dft(odd, q, a), expected+expected_c/2, ('actual R DFT', q, a))
            near(dft(c, q, a), expected_c, ('actual c DFT', q, a))
        pnorm = sum((x*x for x in p), F(0))/q
        rnorm = sum((x*x for x in odd), F(0))/q
        check(pl <= pnorm <= ph, ('exact Parseval/cosecant interval', q))
        check(rl <= rnorm <= rh, ('exact odd Parseval interval', q))
    cycle_count = 0
    for query in finite_cycle_cases:
        _, M, q, a, kind = query;M, q, a, kind = map(int, (M, q, a, kind))
        v = profile(M, kind);active = [(k, w) for k, w in enumerate(v) if w]
        L = math.lcm(q, *(k for k, _ in active))
        check(L <= 60000, ('cycle resource cap', query, L))
        y = [sum((F(2, 3)*w*(n % k-F(k-1, 2)) for k, w in active), F(0)) for n in range(L)]
        g = [y[n]-y[n-1] for n in range(L)]
        r = results[query]
        ey = complex(float((r['y_real_lower']+r['y_real_upper'])/2),
                     float((r['y_imag_lower']+r['y_imag_upper'])/2))
        near(dft(y, q, a), ey, ('complete finite potential cycle', query, L))
        near(dft(g, q, a), float(r['g_lower']), ('complete finite increment cycle', query, L))
        near(abs(ey)**2, float((r['y_mass_lower']+r['y_mass_upper'])/2), ('spectral squared modulus', query))
        cycle_count += 1
    cli_count = 0
    if args.bin:
        binary = str(Path(args.bin).resolve())
        selected = [('C', str(M), str(q), '-1', str(full))
                    for M in (2, 12, 240) for q in (2, 3, 6, 12, 120, 239, 240) for full in (0, 1)]
        for query in selected:
            _, M, q, a, full = query
            cmd = [binary, 'weighted-remainder-state', 'fourier', q, a, M, 'full' if full == '1' else 'finite']
            run = subprocess.run(cmd, capture_output=True, text=True)
            check(run.returncode == 0, (cmd, run.stderr))
            data = dict(line.split('=', 1) for line in run.stdout.splitlines() if '=' in line)
            check(data['mode'] == cmd[-1], ('CLI mode', cmd))
            for k, value in results[query].items():
                check(F(data[k]) == value, ('CLI endpoint', cmd, k))
            check(F(data['p_real']) == F(-1, 2) and F(data['c_real']) == 1 and F(data['g_imag']) == 0, cmd)
            cli_count += 1
        bad = [[], ['2', '1', '2'], ['1', '1', '2', 'full'], ['241', '1', '2', 'full'],
               ['2', '0', '2', 'full'], ['6', '2', '2', 'finite'], ['2', '1/2', '2', 'full'],
               ['2', '+1', '2', 'full'], ['2', '-', '2', 'full'], ['2', '1', '1', 'full'],
               ['2', '1', '241', 'full'], ['2', '1', '2', 'other'], ['2', '1', '2', 'full', 'extra']]
        for tail in bad:
            run = subprocess.run([binary, 'weighted-remainder-state', 'fourier', *tail], capture_output=True, text=True)
            check(run.returncode != 0 and 'fourier requires' in run.stderr, ('invalid CLI', tail, run.stdout, run.stderr))
            cli_count += 1
    print(f'PASS: {checks} checks; {len(queries)} API records; {edge_count} C edge assertions; '
          f'{len(trig)} trigonometric intervals; {len(rows)} complete conductor tables; '
          f'{cycle_count} complete finite cycle transforms; {cli_count} CLI cases.')
    print(f'Maximum scaled direct DFT error={maximum_dft_error:.3e}; tolerance=5e-11. '
          'Machin/full-angle decimal oracle and exact expanded-polynomial grid checks are independent.')
    print('Infinite containment is separate checked Lean evidence; finite DFTs do not prove a limiting law.')


if __name__ == '__main__':
    main()
