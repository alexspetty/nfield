#!/usr/bin/env python3
"""Independent complex phase and full unit-group character checks.

The reference adjoins unit-group generators generically; it does not use
the production prime-power/CRT decomposition or its primitive roots.
"""
import argparse
from collections import Counter
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm
from pathlib import Path
import subprocess
from test_weighted_remainder_fourier import exact_grid_reference, trig_reference, dec

getcontext().prec = 90
checks = 0


def check(ok, why):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(why)


@lru_cache(None)
def phase_reference(r):
    if not r:
        return F(1), F(1), F(0), F(0)
    sl, su, cl, cu = exact_grid_reference(r.denominator, r.numerator)
    def square(l, u):
        return (F(0) if l <= 0 <= u else min(l*l, u*u)), max(l*l, u*u)
    cl2, cu2 = square(cl, cu)
    sl2, su2 = square(sl, su)
    products = [x*y for x in (sl, su) for y in (cl, cu)]
    return cl2-su2, cu2-sl2, 2*min(products), 2*max(products)


def unit_characters(q):
    units = {a for a in range(q) if gcd(a, q) == 1}
    subgroup = {1}
    characters = [{1: F(0)}]
    while subgroup != units:
        g = min(units-subgroup)
        r, v = 1, g
        while v not in subgroup:
            r += 1
            v = v*g % q
        powers = [pow(g, j, q) for j in range(r)]
        enlarged = {h*p % q for h in subgroup for p in powers}
        check(len(enlarged) == len(subgroup)*r, ('disjoint generic cosets', q, g, r))
        new = []
        for chi in characters:
            for branch in range(r):
                theta = (chi[v]+branch)/r
                row = {h*p % q: (chi[h]+j*theta) % 1 for h in subgroup for j, p in enumerate(powers)}
                check(set(row) == enlarged, ('generic extension domain', q))
                new.append(row)
        subgroup, characters = enlarged, new
    check(len(characters) == len(units), ('generic dual order', q))
    return sorted(units), characters


def residue_order(a, q):
    n, value = 1, a % q
    while value != 1:
        n += 1
        value = value*a % q
    return n


def conductor(q, chi):
    for d in range(1, q+1):
        if q % d:
            continue
        fibres = {}
        for a, phase in chi.items():
            residue = a % d
            if residue in fibres and fibres[residue] != phase:
                break
            fibres[residue] = phase
        else:
            return d
    raise AssertionError(('no conductor', q))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--driver', required=True)
    args = ap.parse_args()
    phases = [(q, a) for q in range(1, 241) for a in range(q)]
    phases += [(0, 0), (241, 0), (1, 1), (240, 240), (240, 2**32-1)]
    tables = [0, 1, *range(2, 241), 513]
    inputs = [f'P {q} {a}' for q, a in phases]+[f'T {q} 0' for q in tables]
    run = subprocess.run([str(Path(args.driver).absolute())], input='\n'.join(inputs)+'\n',
                         text=True, capture_output=True)
    check(run.returncode == 0, ('driver exit', run.returncode, run.stderr))
    lines = iter(run.stdout.splitlines())
    edge_line = next(lines)
    check(edge_line.startswith('EDGES '), ('edge record', edge_line))
    edges = int(edge_line.split()[1])
    for q, a in phases:
        row = next(lines).split()
        valid = 1 <= q <= 240 and a < q
        check(row[:2] == ['P', str(int(valid))], ('phase admission', q, a))
        if not valid:
            check(len(row) == 2, ('invalid phase output', q, a))
            continue
        check(len(row) == 6, ('phase fields', q, a))
        values = tuple(map(F, row[2:]))
        check(values == phase_reference(F(a, q)), ('exact double-angle endpoints', q, a))
        check(all(str(F(x)) == x for x in row[2:]), ('canonical phase', q, a))
        rl, ru, il, iu = values
        check(rl <= ru and il <= iu and ru-rl < F(1, 10**14) and iu-il < F(1, 10**14), ('phase width', q, a))
        if a == 0:
            sine, cosine = D(0), D(1)
        elif 2*a == q:
            sine, cosine = D(0), D(-1)
        else:
            sine, cosine = trig_reference(2*F(a, q))
        check(dec(rl) <= cosine <= dec(ru) and dec(il) <= sine <= dec(iu), ('independent full-angle series', q, a))
    character_count = 0
    induced_odd = 0
    maximum_denominator = 0
    for q in tables:
        row = next(lines).split()
        valid = 2 <= q <= 240
        check(row[:2] == ['T', str(int(valid))], ('table admission', q))
        if not valid:
            check(len(row) == 2, ('failed table output', q))
            continue
        q_actual, count, denominator = map(int, row[2:])
        units, expected = unit_characters(q)
        orders = {a: residue_order(a, q) for a in units}
        exponent = lcm(*orders.values())
        check((q_actual, count, denominator) == (q, len(units), exponent), ('full unit-group metadata', q))
        check(1 <= denominator <= 240, ('phase kernel domain', q, denominator))
        maximum_denominator = max(maximum_denominator, denominator)
        wanted = {}
        for chi in expected:
            phases_row = tuple(-1 if a not in chi else int(chi[a]*denominator) for a in range(q))
            check(all((chi[a]*denominator).denominator == 1 for a in units), ('exact common denominator', q))
            check(chi[q-1] in (F(0), F(1, 2)), ('reference parity', q))
            wanted[phases_row] = conductor(q, chi), int(chi[q-1] == F(1, 2))
        check(len(wanted) == count, ('distinct generic characters', q))
        seen = set()
        columns = {a: Counter() for a in units}
        for ch in range(count):
            data = next(lines).split()
            check(data[0] == 'R' and len(data) == q+4, ('character record width', q, ch))
            index, level, odd = map(int, data[1:4])
            character = tuple(map(int, data[4:]))
            check(index == ch and character not in seen, ('character index and uniqueness', q, ch))
            check(character in wanted and wanted[character] == (level, odd), ('generic group and induced conductor', q, ch))
            seen.add(character)
            for a in units:
                columns[a][character[a]] += 1
            if odd and level < q:
                induced_odd += 1
        check(seen == set(wanted), ('all characters retained', q))
        for a in units:
            expected_counts = Counter({k*(denominator//orders[a]): count//orders[a] for k in range(orders[a])})
            check(columns[a] == expected_counts, ('exact column orthogonality root multiplicities', q, a))
        character_count += count
    check(next(lines, None) is None, 'no extra driver records')
    check(induced_odd > 0, 'induced odd characters exercised')
    print(f'PASS complex phases and full unit groups: {checks} checks, {len(phases)} phase API cases, '
          f'{len(tables)} table API cases, {edges} C edge checks, {character_count} characters, '
          f'{induced_odd} induced odd characters, maximum phase denominator {maximum_denominator}.')


if __name__ == '__main__':
    main()
