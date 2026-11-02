"""Independent Fraction oracle for the canonical GMP API and command output."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--bin", required=True)
parser.add_argument("--driver", required=True)
args = parser.parse_args()
binary = str(Path(args.bin).resolve())
driver = str(Path(args.driver).resolve())
checks = 0


def require(condition, message):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(message)


def saw(x):
    frac = x - x.numerator // x.denominator
    return frac - Q(1, 2) if frac else Q(0)


def response(n, x):
    return 2 * sum((saw(r * x) for r in range(1, n + 1)), Q(0))


def breaks(periods):
    return sorted({Q(j, r) for r in periods for j in range(r + 1)})


def direct_overlap(r, s):
    points = breaks([r, s])
    total = Q(0)
    for left, right in zip(points, points[1:]):
        width, middle = right - left, (left + right) / 2
        total += width * saw(r * middle) * saw(s * middle) + r * s * width**3 / 12
    return total


def direct_energy(n):
    if not n:
        return Q(0)
    points = breaks(range(1, n + 1))
    slope = n * (n + 1)
    return sum(((right - left) * response(n, (left + right) / 2)**2 +
                slope**2 * (right - left)**3 / 12
                for left, right in zip(points, points[1:])), Q(0))


# Triangular reciprocal budgets recover the weights without a coprime loop.
weights = [Q(0)] * 241
harmonic = Q(0)
for n in range(1, 241):
    weights[n] = (n * harmonic - sum((d**3 * weights[d] for d in range(1, n)
                                      if n % d == 0), Q(0))) / n**3
    harmonic += Q(1, n)

energy = {n: direct_energy(n) for n in range(25)}
mass = [sum(weights[2:m+1], Q(0)) for m in range(241)]


def amplitude_bounds(q, m):
    lower = sum((weights[k] for k in range(q, m+1, q)), Q(0))
    return lower, lower + 1 - mass[m]


output = subprocess.check_output([driver], text=True)
records = Counter()
intervals = {}
for line in output.splitlines():
    fields = line.split()
    kind = fields[0]
    records[kind] += 1
    if kind == "invalid-input-and-alias-checks":
        require(fields[1] == "PASS", line)
        continue
    value = Q(fields[-1])
    indices = list(map(int, fields[1:-1]))
    if kind == "weight":
        expected = weights[indices[0]]
    elif kind == "capacity":
        expected = energy[indices[0]]
    elif kind == "ramp":
        expected = direct_overlap(*indices)
    elif kind == "midpoint":
        r, a, d = indices
        expected = saw(r * Q(a, d))
    elif kind == "response":
        n, a, d = indices
        expected = response(n, Q(a, d))
    elif kind in ("amplitude_lower", "amplitude_upper"):
        q, m = indices
        lower, upper = amplitude_bounds(q, m)
        expected = lower if kind == "amplitude_lower" else upper
        intervals.setdefault((q, m), {})[kind] = value
    else:
        raise AssertionError("Unknown driver output: " + line)
    require(value == expected, f"{line}: expected {expected}")
require(records == Counter(weight=241, capacity=25, ramp=1025,
                           midpoint=13*13*27, response=13*13*27+1,
                           amplitude_lower=31*31+36, amplitude_upper=31*31+36,
                           **{"invalid-input-and-alias-checks": 1}), records)

for (q, m), endpoints in intervals.items():
    lower, upper = endpoints["amplitude_lower"], endpoints["amplitude_upper"]
    require(0 <= lower <= upper <= 1, (q, m, "valid unit-mass interval"))
    require(upper-lower == 1-mass[m], (q, m, "exact omitted mass"))
    partial240 = amplitude_bounds(q, 240)[0]
    require(lower <= partial240 <= upper, (q, m, "independent later partial sum"))
    if q == 2:
        require(lower <= Q(1, 2) <= upper, (q, m, "known conductor-two value"))
    if (q, m-1) in intervals:
        previous = intervals[q, m-1]
        require(previous["amplitude_lower"] <= lower and
                upper <= previous["amplitude_upper"], (q, m, "nested enclosures"))

for n in range(25):
    command = [binary, "weighted-remainder-state", "boundary", str(n)]
    text = subprocess.check_output(command, text=True)
    atoms = {}
    for line in text.splitlines():
        fields = line.split()
        if len(fields) == 2 and "/" in fields[0]:
            atom = Q(fields[0])
            require(atom not in atoms, (n, "duplicate reduced atom", atom))
            atoms[atom] = int(fields[1])
    direct = Counter(Q(j, r) for r in range(1, n + 1) for j in range(r))
    require(atoms == direct, (n, "source measure mismatch"))
    require(sum(atoms.values()) == n * (n + 1) // 2, (n, "total source mass"))
    values = dict(line.split(maxsplit=1) for line in text.splitlines()
                  if line.startswith(("capacity ", "deficit ")))
    require(Q(values["capacity"]) == energy[n], (n, "CLI energy"))
    require(Q(values["deficit"]) == n - energy[n], (n, "CLI deficit"))

for r, s in [(1, 1), (2, 3), (6, 4), (12, 12), (239, 240)]:
    text = subprocess.check_output([binary, "weighted-remainder-state", "ramp", str(r), str(s)], text=True)
    integral = next(line.split()[1] for line in text.splitlines() if line.startswith("integral "))
    require(Q(integral) == direct_overlap(r, s), (r, s, "CLI ramp"))

for q, m in [(2, 2), (3, 6), (7, 2), (31, 32), (239, 240), (240, 240)]:
    text = subprocess.check_output([binary, "weighted-remainder-state", "amplitude", str(q), str(m)], text=True)
    values = dict(line.split(maxsplit=1) for line in text.splitlines()
                  if line.startswith(("lower ", "upper ", "width ")))
    lower, upper = amplitude_bounds(q, m)
    require(Q(values["lower"]) == lower and Q(values["upper"]) == upper and
            Q(values["width"]) == upper-lower, (q, m, "CLI amplitude enclosure"))

for operands in [["boundary", "-1"], ["boundary", "241"], ["boundary", "1x"],
                 ["boundary", "9999999999999999999999999999999999999"],
                 ["boundary"], ["boundary", "1", "extra"],
                 ["ramp", "0", "1"], ["ramp", "1", "241"], ["ramp", "1", "2x"],
                 ["ramp", "1"], ["ramp", "1", "2", "extra"],
                 ["amplitude", "1", "2"], ["amplitude", "2", "1"],
                 ["amplitude", "241", "2"], ["amplitude", "2", "241"],
                 ["amplitude", "2", "2x"], ["amplitude", "-2", "2"],
                 ["amplitude", "2"], ["amplitude", "2", "2", "extra"]]:
    result = subprocess.run([binary, "weighted-remainder-state", *operands],
                            text=True, capture_output=True)
    require(result.returncode != 0 and "Use boundary" in result.stderr, operands)

print(f"PASS: {checks} independent exact rational and interface checks.")
print("Weights use triangular budgets; atoms use unreduced addresses; energy uses actual nonuniform jump cells.")
print("Signed phases, midpoint jumps, in-place output, invalid domains and visitor cancellation are covered.")
print("Amplitude endpoints use independently recovered weights; omitted mass, nesting, later partial sums and q>M are checked.")
print("Finite admitted domains only; no infinite or asymptotic claim is inferred.")
