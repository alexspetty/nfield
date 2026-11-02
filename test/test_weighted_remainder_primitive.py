"""Independent rational lattice and triangular-budget oracle.

Production traverses the primitive tree; this oracle enumerates the square
and tests gcd. It reconstructs weights by triangular divisor budgets rather
than importing the production reciprocal sums or Mobius algorithm.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser()
parser.add_argument("--bin", default="./nfield")
parser.add_argument("--driver", required=True)
parser.add_argument("--skip-cli", action="store_true")
args = parser.parse_args()
driver = str(Path(args.driver).resolve())
binary = str(Path(args.bin).resolve())
checks = 0
cli_checks = 0
records = 0


def check(condition, context):
    global checks
    checks += 1
    assert condition, context


harmonics = [F(0)]
weights = [F(0)]
for n in range(1, 241):
    harmonics.append(harmonics[-1] + F(1, n))
    proper = sum((d ** 3 * weights[d] for d in range(1, n) if n % d == 0), F(0))
    weights.append((n * harmonics[n - 1] - proper) / n ** 3)
retained = [sum(weights[:n + 1], F(0)) for n in range(241)]
weighted_mass = [sum((k * weights[k] for k in range(n + 1)), F(0)) for n in range(241)]
deficit_bound = [F(2, 3) * (weighted_mass[n] + n * (1 - retained[n])) for n in range(241)]
# Independent direct gcd energies, extended by one boundary row at a time.
capacity = [F(0)]
for n in range(1, 241):
    capacity.append(capacity[-1] + F(1, 3) +
                    2 * sum((F(gcd(r, n) ** 2, 3 * r * n) for r in range(1, n)), F(0)))


def potential(a, b):
    return F(a + b, a * a * b * b)


def node(a, b):
    root = potential(a, b)
    left = potential(a, a + b)
    right = potential(a + b, b)
    # Derive the loss by subtraction, independently of the production kernel.
    return root, left, right, root - left - right


@lru_cache(None)
def square(m):
    pairs = [(a, b) for a in range(1, m + 1) for b in range(1, m + 1) if gcd(a, b) == 1]
    mass = sum((F(1, a * b * (a + b)) for a, b in pairs), F(0))
    frontier = sum((potential(a, a + b) + potential(a + b, b)
                    for a, b in pairs if a + b > m), F(0))
    addresses = sum((F(1, a * (a + b) ** 2) for a, b in pairs), F(0))
    return len(pairs), mass, frontier, 2 * (harmonics[m] + 1) / m, addresses


result = subprocess.run([driver], text=True, capture_output=True)
if result.returncode:
    print(result.stderr, file=sys.stderr)
    raise SystemExit(result.returncode)
edge_count = 0
actual_weights = {}
for line in result.stdout.splitlines():
    fields = line.split()
    kind = fields[0]
    if kind == "edge_checks":
        edge_count = int(fields[1])
        check(edge_count > 0, line)
        continue
    records += 1
    n = int(fields[1])
    if kind == "node":
        b = int(fields[2])
        values = tuple(map(F, fields[3:]))
        for value, reference in zip(values, node(n, b), strict=True):
            check(value == reference, line)
        check(values[0] == sum(values[1:]), line)
        check(values[3] == F(1, n * b * (n + b)) > 0, line)
    elif kind == "address":
        b = int(fields[2])
        check(F(fields[3]) == F(1, n * (n + b) ** 2), line)
    elif kind == "tree":
        values = int(fields[2]), *map(F, fields[3:])
        for value, reference in zip(values, square(n)[:4], strict=True):
            check(value == reference, line)
        _, mass, frontier, upper = values
        check(mass + frontier == 2, line)
        check(0 <= frontier <= upper, line)
        check(0 < mass < 2, line)
        check(mass / 2 == square(n)[4], line)
    elif kind == "weight":
        check(F(fields[2]) == weights[n], line)
        check(F(fields[3]) == weights[n], line)
        with localcontext() as context:
            context.prec = 70
            reference = Decimal(weights[n].numerator) / Decimal(weights[n].denominator)
            check(abs(Decimal(fields[4]) - reference) <= Decimal("1e-16") * (1 + abs(reference)), line)
        check(weights[n] >= 0, line)
        actual_weights[n] = F(fields[2])
    elif kind == "mass":
        mass, omitted = map(F, fields[2:])
        check(mass == retained[n], line)
        check(omitted == 1 - retained[n], line)
        check(0 <= mass < 1 and 0 < omitted <= 1, line)
        if n:
            check(mass - retained[n - 1] == weights[n], line)
    elif kind == "mass_budget":
        values = tuple(map(F, fields[2:]))
        for value, reference in zip(values, (retained[n], 1 - retained[n], weighted_mass[n], deficit_bound[n]), strict=True):
            check(value == reference, line)
        check(n - capacity[n] <= values[3], line)
    elif kind == "budget":
        check(F(fields[2]) == n * harmonics[n - 1], line)
    else:
        raise AssertionError(line)

for d in range(2, 241):
    for m in range(1, 240 // d + 1):
        check(actual_weights[d * m] <= actual_weights[d] / m ** 2 * (1 + harmonics[m - 1] / 2), (d, m))


def run_cli(operands):
    global cli_checks
    text = subprocess.check_output([binary, "weighted-remainder-state", *map(str, operands)], text=True)
    cli_checks += 1
    return {words[0]: words[1:] for line in text.splitlines() if (words := line.split())}


if not args.skip_cli:
    for m in (1, 2, 3, 6, 12, 31, 120, 240):
        values = run_cli(("tree", m))
        reference = square(m)
        check(int(values["nodes"][0]) == reference[0], m)
        for key, expected in zip(("primitive_pair_mass", "outgoing_mass", "harmonic_upper_bound", "primitive_address_mass"), reference[1:], strict=True):
            check(F(values[key][0]) == expected, (m, key))
    for a, b in ((1, 1), (2, 3), (6, 4), (119, 120), (239, 240), (240, 240)):
        values = run_cli(("tree-node", a, b))
        for key, expected in zip(("potential", "left_child", "right_child", "loss"), node(a, b), strict=True):
            check(F(values[key][0]) == expected, (a, b, key))
        check(F(values["address_mass"][0]) == F(1, a * (a + b) ** 2), (a, b))
    for n in (0, 1, 2, 6, 12, 31, 120, 239, 240):
        values = run_cli(("weight", n))
        check(F(values["weight"][0]) == weights[n], n)
        check(F(values["budget_inverse"][0]) == weights[n], n)
        check(F(values["forcing_coefficient"][0]) == n * weights[n], n)
        values = run_cli(("mass", n))
        check(F(values["retained_mass"][0]) == retained[n], n)
        check(F(values["omitted_mass"][0]) == 1 - retained[n], n)
        check(F(values["weighted_mass"][0]) == weighted_mass[n], n)
        check(F(values["deficit_upper_bound"][0]) == deficit_bound[n], n)
        if n:
            values = run_cli(("budget", n))
            check(F(values["budget"][0]) == n * harmonics[n - 1], n)
    for action in ("tree", "tree-node", "weight", "budget", "mass"):
        for bad in ("-1", "+1", " 1", "241", "1x", "999999999999999999999999999999"):
            operands = [action, bad] + (["1"] if action == "tree-node" else [])
            response = subprocess.run([binary, "weighted-remainder-state", *operands], text=True, capture_output=True)
            cli_checks += 1
            check(response.returncode == 1 and bool(response.stderr), operands)
        for operands in ([action], [action, "1", "1", "1"]):
            response = subprocess.run([binary, "weighted-remainder-state", *operands], text=True, capture_output=True)
            cli_checks += 1
            check(response.returncode == 1, operands)
    for operands in (("tree", "0"), ("tree-node", "1", "0"), ("budget", "0")):
        response = subprocess.run([binary, "weighted-remainder-state", *operands], text=True, capture_output=True)
        cli_checks += 1
        check(response.returncode == 1, operands)

print(f"primitive oracle PASS: {checks + edge_count} checks; {records} API records; {edge_count} C edge checks; {cli_checks} CLI cases")
print("Exact rational square/frontier, triangular weights, Mobius inverse, divisor budgets and mass complements; finite domains only.")
print("Long-double weights compared separately at 1e-16*(1+abs(reference)); no floating enclosure or infinite law inferred.")
