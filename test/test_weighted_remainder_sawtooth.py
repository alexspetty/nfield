"""Independent exact oracle: floor fractions, Euclidean reciprocity and cycles.

Production sums a Dedekind table and reduces a row pairing to the gcd.
This oracle evaluates Dedekind sums recursively by reciprocity and checks
pairings on every point of the full lcm cycle. Conditional means enumerate
the actual residue fiber. It imports no production implementation.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser()
parser.add_argument("--bin", default="./nfield")
parser.add_argument("--driver", required=True)
parser.add_argument("--skip-cli", action="store_true")
args = parser.parse_args()
binary = str(Path(args.bin).resolve())
driver = str(Path(args.driver).resolve())
checks = records = cli_checks = 0
ll_min, ll_max = -(1 << 63), (1 << 63) - 1


def check(condition, context):
    global checks
    checks += 1
    assert condition, context


def saw(d, a, n):
    z = F(a * n, d)
    fractional = z - z.numerator // z.denominator
    return fractional - F(1, 2) if fractional else F(0)


@lru_cache(None)
def dedekind(d, a):
    a %= d
    if d == 1:
        return F(0)
    assert gcd(a, d) == 1
    # s(a,d)+s(d,a)=-1/4+(a/d+d/a+1/(ad))/12.
    return -F(1, 4) + (F(a, d) + F(d, a) + F(1, a * d)) / 12 - dedekind(a, d % a)


@lru_cache(None)
def cycle_pair(d, a, e, b):
    period = lcm(d, e)
    # A common denominator avoids per-point rational allocation, but every
    # lcm residue is still visited independently of the gcd pairing formula.
    numerator = 0
    for n in range(period):
        u, v = (a * n) % d, (b * n) % e
        first = 2 * u - d if u else 0
        second = 2 * v - e if v else 0
        numerator += first * second
    return F(numerator, 4 * d * e * period)


@lru_cache(None)
def fiber_mean(d, a, q, t):
    return sum((saw(d, a, n) for n in range(t % q, d, q)), F(0)) / (d // q)


# Cross-check the reciprocal oracle from its independent floor definition.
for d in range(1, 25):
    for a in range(d):
        if gcd(a, d) == 1:
            check(dedekind(d, a) == sum((saw(d, 1, n) * saw(d, a, n)
                                       for n in range(d)), F(0)), ("reciprocity", d, a))

result = subprocess.run([driver], text=True, capture_output=True)
if result.returncode:
    print(result.stderr, file=sys.stderr)
    raise SystemExit(result.returncode)
edges = 0
seen_dedekind = {}
seen_gram = {}
for line in result.stdout.splitlines():
    parts = line.split()
    kind = parts[0]
    if kind == "edge_checks":
        edges = int(parts[1])
        check(edges > 0, line)
        continue
    records += 1
    numbers = tuple(map(int, parts[1:-1]))
    value = F(parts[-1])
    if kind == "row":
        d, a, n = numbers
        check(value == saw(d, a, n), line)
        check(-F(1, 2) < value < F(1, 2), line)
        check(value == -saw(d, a, -n), line)
    elif kind == "dedekind":
        d, a = numbers
        check(value == dedekind(d, a % d), line)
        check(value == -dedekind(d, (-a) % d), line)
        seen_dedekind[d, a % d] = value
    elif kind == "gram":
        d, a, e, b = numbers
        check(value == cycle_pair(d, a % d, e, b % e), line)
        if d == e:
            check(value == dedekind(d, b * pow(a, -1, d) % d) / d, line)
        if gcd(d, e) == 1:
            check(value == 0, line)
        seen_gram[d, a % d, e, b % e] = value
    elif kind == "mean":
        d, a, q, t = numbers
        check(value == fiber_mean(d, a % d, q, t % q), line)
    else:
        raise AssertionError(line)

for (d, a), value in seen_dedekind.items():
    inverse = pow(a, -1, d)
    check(value == seen_dedekind[d, inverse], ("inverse", d, a))
    if a == 1:
        check(value == F((d - 1) * (d - 2), 12 * d), ("diagonal", d))
for (d, a, e, b), value in seen_gram.items():
    if (e, b, d, a) in seen_gram:
        check(value == seen_gram[e, b, d, a], ("symmetry", d, a, e, b))


def cli(command):
    global cli_checks
    result = subprocess.run([binary, "weighted-remainder-state", *map(str, command)],
                            text=True, capture_output=True)
    cli_checks += 1
    return result


if not args.skip_cli:
    good = [
        (("sawtooth", 5, 2, 1), "value", saw(5, 2, 1)),
        (("sawtooth", 5, -2, -1), "value", saw(5, -2, -1)),
        (("sawtooth", 5, ll_min, ll_max), "value", saw(5, ll_min, ll_max)),
        (("sawtooth", 1, ll_min, ll_max), "value", F(0)),
        (("sawtooth", 2, 1, 1), "value", F(0)),
        (("dedekind", 5, 1), "dedekind_sum", F(1, 5)),
        (("dedekind", 5, -1), "dedekind_sum", F(-1, 5)),
        (("dedekind", 1, 0), "dedekind_sum", F(0)),
        (("dedekind", 239, ll_min), "dedekind_sum", dedekind(239, ll_min % 239)),
        (("gram", 6, 1, 9, 1), "haar_pairing", F(1, 324)),
        (("gram", 6, -1, 9, 1), "haar_pairing", F(-1, 324)),
        (("gram", 1, 0, 240, 1), "haar_pairing", F(0)),
        (("gram", 239, ll_min, 240, ll_max), "haar_pairing", F(0)),
        (("sawtooth-mean", 6, 1, 3, 1), "conditional_mean", F(-1, 12)),
        (("sawtooth-mean", 6, -1, 3, -1), "conditional_mean", F(-1, 12)),
        (("sawtooth-mean", 240, ll_max, 120, ll_min), "conditional_mean",
         fiber_mean(240, ll_max % 240, 120, ll_min % 120)),
        (("sawtooth-mean", 1, 0, 1, ll_min), "conditional_mean", F(0)),
    ]
    for command, field, expected in good:
        result = cli(command)
        check(result.returncode == 0, (command, result.stderr))
        output = dict(line.split(maxsplit=1) for line in result.stdout.splitlines() if " " in line)
        check(F(output[field]) == expected, (command, result.stdout))
    seeds = [("sawtooth", 5, 1, 2), ("dedekind", 5, 1),
             ("gram", 6, 1, 9, 1), ("sawtooth-mean", 6, 1, 3, 1)]
    invalid = []
    for seed in seeds:
        invalid.extend([seed[:-1], (*seed, "extra")])
        for text in ["", "0", "-1", "+5", "241", "999999999999999999999", " 5", "5 ", "5x"]:
            invalid.append((seed[0], text, *seed[2:]))
        for text in ["", "-", "+1", "1x", " 1", "1 ", str(ll_min - 1), str(ll_max + 1), "0"]:
            invalid.append((*seed[:2], text, *seed[3:]))
    invalid.extend([
        ("gram", 6, 2, 5, 1), ("gram", 5, 1, 6, 2), ("gram", 5, 1, 0, 1),
        ("gram", 5, 1, 241, 1), ("gram", 5, 1, 6, str(ll_max + 1)),
        ("sawtooth-mean", 6, 2, 1, 0), ("sawtooth-mean", 5, 1, 3, 0),
        ("sawtooth-mean", 5, 1, 0, 0), ("sawtooth-mean", 5, 1, 241, 0),
        ("sawtooth-mean", 5, 1, 1, str(ll_min - 1)), ("sawtooth", 5, 1, str(ll_max + 1)),
    ])
    for command in invalid:
        result = cli(command)
        check(result.returncode != 0 and result.stderr, (command, result.stdout))

print(f"{checks + edges} independent sawtooth checks passed; {records} API records; "
      f"{edges} C edge checks; {cli_checks} CLI cases.")
