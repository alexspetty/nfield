#!/usr/bin/env python3
"""Independent powers, Decimal transcendental values and boundary checks."""
import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from math import factorial, gcd
from pathlib import Path
import random
import subprocess

getcontext().prec = 180
GRID = 10**24
checks = 0


def check(ok, detail):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(detail)


def dec(x):
    return D(x.numerator)/D(x.denominator)


def rounded(x, upward=False):
    x *= GRID
    return F(-(-x.numerator//x.denominator) if upward else x.numerator//x.denominator, GRID)


def polynomial(r):
    lo = sum((2*r**(2*j+1)/(2*j+1) for j in range(24)), F())
    return lo, lo+2*r**49/(1-r*r)


def log_reference(x):
    # Bit lengths choose the scale directly, rather than repeating the C loop.
    b = x.numerator.bit_length()-x.denominator.bit_length()
    scale = F(2)**b
    if scale > x:
        b -= 1
        scale /= 2
    r = (x-scale)/(x+scale)
    lo, hi = polynomial(r)
    two = sorted(b*y for y in polynomial(F(1, 3)))
    return rounded(lo+two[0]), rounded(hi+two[1], True)


def exp_reference(a, b):
    error = F(25, 24*factorial(24))
    lo = sum((a**k/factorial(k) for k in range(24)), F())-error
    hi = sum((b**k/factorial(k) for k in range(24)), F())+error
    return max(F(1), rounded(max(F(1), lo))), rounded(hi, True)


def admitted(text, allow_zero=False):
    values = text.split('/')
    n, d = int(values[0]), int(values[1]) if len(values) == 2 else 1
    return n >= int(not allow_zero) and d > 0 and n.bit_length() <= 256 and d.bit_length() <= 256 and gcd(n, d) == 1


def main():
    ap = argparse.ArgumentParser();ap.add_argument('--driver', required=True);args = ap.parse_args()
    queries = [('L', str(F(2)**b)) for b in range(-255, 256)]
    queries += [('L', str(F(a, b))) for a in (1, 2, 3, 127, 239, 240, 2**255-1) for b in (1, 2, 3, 239, 2**255+1)]
    queries += [('L', str(F(2**255+d, 2**255))) for d in (-1, 1)]
    rng = random.Random(20260914)
    queries += [('L', str(F(rng.getrandbits(256) or 1, rng.getrandbits(256) or 1))) for _ in range(160)]
    queries += [('E', str(F(a, 240)), str(F(a, 240))) for a in range(241)]
    queries += [('E', str(F(a, 240)), str(F(b, 240))) for a, b in [(0, 240), (1, 239), (139, 140), (0, 1)]]
    queries += [('E', '0', str(F(1, 2**255))), ('E', str(F(2**255-1, 2**255)), '1')]
    queries += [('L', x) for x in ['0', '-1', '2/2', '1/0', '1/-2', str(2**256), '1/'+str(2**256)]]
    queries += [('E', a, b) for a, b in [('-1', '1'), ('0', '2'), ('3/4', '1/2'), ('2/2', '1'), ('0', '1/0')]]
    run = subprocess.run([str(Path(args.driver).absolute())],
        input=''.join(' '.join(q)+'\n' for q in queries), text=True, capture_output=True, timeout=240)
    check(run.returncode == 0 and not run.stderr, ('driver', run.returncode, run.stderr))
    lines = run.stdout.splitlines();check(lines[0] == 'EDGES 68', ('edges', lines[:1]))
    check(len(lines) == len(queries)+1, ('records', len(lines), len(queries)))
    valid_count = 0
    for query, line in zip(queries, lines[1:]):
        parts = line.split();check(parts[0] == query[0], ('operation', query))
        if query[0] == 'L':
            valid = admitted(query[1])
        else:
            valid = all(admitted(x, True) for x in query[1:])
            if valid:
                valid = F(query[1]) <= F(query[2]) <= 1
        check(int(parts[1]) == valid, ('admission', query))
        if not valid:
            check(len(parts) == 2, ('failure output', query));continue
        valid_count += 1
        x = F(query[1])
        expected = log_reference(x) if query[0] == 'L' else exp_reference(x, F(query[2]))
        check(parts[2:] == list(map(str, expected)), ('exact rounded polynomial and remainder', query))
        lo, hi = expected
        if query[0] == 'L':
            value = dec(x).ln()
            check(dec(lo) <= value <= dec(hi), ('independent Decimal log', query))
        else:
            check(dec(lo) <= dec(x).exp() <= dec(F(query[2])).exp() <= dec(hi), ('independent Decimal exp', query))
    print(f'PASS rational log and small exp: {checks} independent checks; {valid_count} admitted, {len(queries)-valid_count} rejected; 68 C admission/preservation/alias assertions; exact endpoints plus 180-digit Decimal values.')


if __name__ == '__main__':
    main()
