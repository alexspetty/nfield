"""Independent exact conditional-cycle and normalized-position oracle.

Weights come from triangular harmonic budgets. Conditional coefficients
come from enumerating actual residue fibers, not the production gcd mean.
Later finite cutoffs are additional checks, never evidence of an infinite limit.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import lcm
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--bin")
parser.add_argument("--driver", required=True)
args = parser.parse_args()
driver = str(Path(args.driver).resolve())
checks = 0


def require(condition, context):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(context)


weights, harmonic = [Q(0)]*241, Q(0)
for n in range(1, 241):
    weights[n] = (n*harmonic-sum((d**3*weights[d] for d in range(1, n)
                                 if n%d == 0), Q(0)))/n**3
    harmonic += Q(1, n)
masses = [sum(weights[:m+1], Q(0)) for m in range(241)]


@lru_cache(None)
def row_mean(L, a, k):
    a %= L
    cycle = lcm(L, k)
    residues = range(a, cycle, L)
    return Q(sum(n%k for n in residues), len(residues))-Q(k-1, 2)


@lru_cache(None)
def components(L, a):
    a %= L
    c, m, relative = [Q(0)]*241, [Q(0)]*241, [Q(0)]*241
    for k in range(2, 241):
        c[k] = -Q(2, 3)*weights[k]*row_mean(L, 0, k)
        m[k] = Q(2, 3)*weights[k]*row_mean(L, a, k)
        relative[k] = (m[k]+c[k])/(2*c[k]) if c[k] else Q(0)
    # The zero-weight period zero is not a finite residue cycle. Its
    # relative residue is defined by gcd(0,L)=L but its probability is zero.
    relative[0] = Q(a, L-1) if L > 1 else Q(0)
    return c, m, relative


@lru_cache(None)
def cylinder(L, a, M):
    c, m, _ = components(L, a%L)
    return sum(c[:M+1], Q(0)), sum(m[:M+1], Q(0)), Q(L-1, 3)*(1-masses[M]), 1-masses[M]


@lru_cache(None)
def event(L, a, M, delta):
    c, _, rel = components(L, a%L)
    return sum((c[k] for k in range(2, M+1) if rel[k] > delta), Q(0))


def position(L, a, M, delta):
    c, m, r, _ = cylinder(L, a, M)
    numerator = event(L, a, M, delta)
    return ((m+c)/2/(c+r), min(Q(1), ((m+c)/2+r)/c),
            numerator/(c+r), min(Q(1), (numerator+r)/c), min(Q(1), r/c))


def weight(L, a, k, M):
    c, _, r, _ = cylinder(L, a, M)
    terms, _, rel = components(L, a%L)
    return terms[k]/(c+r), min(Q(1), terms[k]/c), rel[k]


records = Counter()
for line in subprocess.check_output([driver], text=True).splitlines():
    fields = line.split()
    kind = fields[0]
    records[kind] += 1
    if kind == "edges":
        require(fields[-1] == "PASS" and int(fields[1]) >= 200, line)
        edges = int(fields[1])
        continue
    L, a = map(int, fields[1:3])
    if kind == "cylinder":
        M = int(fields[3]); actual = tuple(map(Q, fields[4:]))
        require(actual == cylinder(L, a, M), ("complete conditional cycle", line))
        c, m, r, tail = actual
        require(r >= 0 and tail > 0, line)
        later_c, later_m, _, _ = cylinder(L, a, 240)
        require(c <= later_c <= c+r, ("later finite alignment", line))
        require(m-r <= later_m <= m+r, ("later finite mean", line))
        require(m+c <= later_m+later_c <= m+c+2*r, ("later finite gap", line))
        require(cylinder(L, -a-1, M)[1] == -m, ("reflection", line))
        require(cylinder(L, a+L, M) == actual, ("periodicity", line))
    elif kind == "position":
        M = int(fields[3]); delta = Q(fields[4]); actual = tuple(map(Q, fields[5:]))
        require(actual == position(L, a, M, delta), ("normalized conditional components", line))
        gl, gu, el, eu, omitted = actual
        require(0 <= gl <= gu <= 1 and 0 <= el <= eu <= 1 and 0 <= omitted <= 1, line)
        c, m, _, _ = cylinder(L, a, 240)
        require(gl <= (m+c)/(2*c) <= gu, ("later finite normalized gap", line))
        require(el <= event(L, a, 240, delta)/c <= eu, ("later finite event", line))
        small_c = cylinder(L, a, M)[0]
        require((c-small_c)/c <= omitted, ("later finite omitted probability", line))
        if delta > 0:
            require(delta*event(L, a, 240, delta) <= (m+c)/2, ("finite Markov bound", line))
    elif kind == "weight":
        k, M = map(int, fields[3:5]); actual = tuple(map(Q, fields[5:]))
        require(actual == weight(L, a, k, M), ("individual full-weight endpoints", line))
        lo, hi, rel = actual
        require(0 <= lo <= hi <= 1 and 0 <= rel <= 1, line)
        require(lo <= components(L, a%L)[0][k]/cylinder(L, a, 240)[0] <= hi, line)
    else:
        raise AssertionError(line)

for L in range(2, 17):
    values = [cylinder(L, a, 24)[1] for a in range(L)]
    require(values.count(min(values)) == 1 and values.index(min(values)) == 0, (L, "unique finite min"))
    require(values.count(max(values)) == 1 and values.index(max(values)) == L-1, (L, "unique finite max"))
    c = cylinder(L, 0, 24)[0]
    require(values[0] == -c and values[-1] == c and sum(values) == 0, (L, "mean and endpoints"))
    terms, _, _ = components(L, 0)
    full_c = cylinder(L, 0, 240)[0]
    require(sum(t/full_c for t in terms) == 1, (L, "finite normalization"))

if args.bin:
    binary = str(Path(args.bin).resolve())

    def query(*parts):
        text = subprocess.check_output([binary, "weighted-remainder-state", *map(str, parts)], text=True)
        return dict(line.split("=", 1) for line in text.splitlines() if "=" in line)

    for L, a, M in [(1,-5,2),(6,1,24),(7,-2,31),(240,10**100+1,240)]:
        c, m, r, t = cylinder(L, a, M)
        out = query("cylinder", L, a, M)
        for key, value in {"finite_alignment":c,"finite_mean":m,"mean_radius":r,
                           "omitted_unit_mass":t,"mean_lower":m-r,"mean_upper":m+r,
                           "alignment_upper":c+r,"absolute_gap_lower":m+c,
                           "absolute_gap_upper":m+c+2*r}.items():
            require(Q(out[key]) == value, (key, out))
        if L >= 2:
            out = query("position", L, a, M, "1/3")
            expected = position(L, a, M, Q(1,3))
            for key,value in zip(["relative_gap_lower","relative_gap_upper","exceedance_lower",
                                   "exceedance_upper","omitted_position_mass_upper"],expected):
                require(Q(out[key]) == value, (key,out))
            out = query("position-weight", L, a, 239, M)
            for key,value in zip(["probability_lower","probability_upper","relative_residue"],weight(L,a,239,M)):
                require(Q(out[key]) == value, (key,out))
    invalid = [("cylinder",0,1,2),("cylinder",241,1,240),("cylinder",2,1,1),
               ("cylinder",2,"1.5",2),("cylinder",2,"+",2),("cylinder",2," 1",2),
               ("position",1,0,2,0),("position",3,0,2,0),("position",2,0,2,"1/0"),
               ("position",2,0,2,"1/-2"),("position",2,0,2,"1/2/3"),
               ("position",2,0,2,"nan"),("position-weight",2,0,241,2),
               ("position",2,0,2),("position-weight",2,0,2),
               ("cylinder",2,0,2,"extra")]
    for parts in invalid:
        p = subprocess.run([binary,"weighted-remainder-state",*map(str,parts)],capture_output=True,text=True)
        require(p.returncode != 0 and "Invalid cylinder query" in p.stderr, (parts,p.stdout,p.stderr))

print(f"Independent conditional-cycle and position oracle: {checks} checks PASS; "
      f"{sum(records.values())-1} API records; {edges} direct C edge checks.")
print("Exact finite arithmetic and later-cutoff checks only; universal containment and limits have separate Lean proofs.")
