"""Independent exact comparison with literal floors and rational midpoint sums.

The C floor loop uses nonnegative machine-integer quotients after reduction.
The second oracle path reconstructs F from the inverse address map and
the midpoint sum, using Python Fraction and arbitrary-size integer phases.
No production implementation or arithmetic helper is imported.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
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
ll_min, ll_max = -(1 << 63), (1 << 63) - 1
checks = records = cli_checks = 0


def check(condition, context):
    global checks
    checks += 1
    assert condition, context


@lru_cache(None)
def floor_lists(p, a):
    a %= p * p
    return sum((((d * (p + 1) + 1) * a) // (p * p) -
                (d * (p + 1) * a) // (p * p) for d in range(p)), 0) - F(a, p)


@lru_cache(None)
def midpoint_sum(p, a):
    # Literal fractional parts, with zero exactly at integers.
    total = F(0)
    for r in range(1, p):
        z = F(r * a, p * p)
        part = z - z.numerator // z.denominator
        if part:
            total += 2 * part - 1
    return total


result = subprocess.run([driver], text=True, capture_output=True)
if result.returncode:
    print(result.stderr, file=sys.stderr)
    raise SystemExit(result.returncode)
edges = 0
seen = set()
for line in result.stdout.splitlines():
    parts = line.split()
    if parts[0] == "edge_checks":
        edges = int(parts[1])
        check(edges > 0, line)
        continue
    check(parts[0] == "sample" and len(parts) == 6, line)
    p, a = map(int, parts[1:3])
    raw, left, right = map(F, parts[3:])
    modulus = p * p
    canonical = a % modulus
    transformed = ((1 - p) * a) % modulus
    inverse = pow(1 - p, -1, modulus)
    check(raw == floor_lists(p, canonical), ("literal floors", line))
    check(raw == midpoint_sum(p, (inverse * a) % modulus), ("inverse midpoint", line))
    check(left == floor_lists(p, transformed), ("transformed floors", line))
    check(right == midpoint_sum(p, a), ("literal midpoint", line))
    check(left == right, ("straightening", line))
    check(raw == -floor_lists(p, (-a) % modulus), ("reflection", line))
    if a % p == 0:
        check(raw == left == right == 0, ("nonunit", line))
    seen.add((p, canonical))
    records += 1

for p in range(2, 44):
    if all(p % d for d in range(2, p)):
        check(all((p, a) in seen for a in range(p * p)), ("exhaustive prime", p))


def cli(*command):
    global cli_checks
    cli_checks += 1
    return subprocess.run([binary, "weighted-remainder-state", *map(str, command)],
                          text=True, capture_output=True)


if not args.skip_cli:
    for p in [2, 3, 5, 31, 43, 127, 239]:
        for a in [0, 1, p, -1, ll_min, ll_max]:
            for action in ["floor", "straighten"]:
                result = cli(action, p, a)
                check(result.returncode == 0, (action, p, a, result.stderr))
                rows = dict(line.split(maxsplit=1) for line in result.stdout.splitlines()[1:])
                check(int(rows["prime"]) == p and int(rows["modulus"]) == p * p, rows)
                check(int(rows["address"]) == a and int(rows["canonical_address"]) == a % (p * p), rows)
                expected = floor_lists(p, a if action == "floor" else ((1 - p) * a) % (p * p))
                check(F(rows["floor_response"]) == expected, rows)
                if action == "straighten":
                    check(int(rows["transformed_address"]) == ((1 - p) * a) % (p * p), rows)
                    check(F(rows["midpoint_response"]) == midpoint_sum(p, a), rows)
                    check(F(rows["difference"]) == 0, rows)
    bad_primes = [0, 1, 4, 9, 49, 121, 240, 241, -3, "+3", " 3", "3x", "", 2**64]
    bad_addresses = ["", "-", "+1", " 1", "1 ", "1x", "0x10", ll_min - 1, ll_max + 1]
    for action in ["floor", "straighten"]:
        for p in bad_primes:
            result = cli(action, p, 1)
            check(result.returncode != 0 and not result.stdout, (action, p, result))
        for a in bad_addresses:
            result = cli(action, 239, a)
            check(result.returncode != 0 and not result.stdout, (action, a, result))
        for command in [(action,), (action, 3), (action, 3, 1, 2)]:
            result = cli(*command)
            check(result.returncode != 0, (command, result))

print(f"floor-response exact checks={checks + edges}; API records={records}; "
      f"C edge checks={edges}; CLI cases={cli_checks}")
print("All prime-square addresses for primes through 43; every nonunit at every prime 2..239; "
      "deterministic phase samples, signed extremes, inverse midpoint reconstruction, "
      "literal floor lists, invalid input and output preservation passed.")
