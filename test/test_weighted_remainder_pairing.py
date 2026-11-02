"""Independent exact boundary-energy and complete-cycle pairing oracle."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, lcm
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--bin", required=True)
parser.add_argument("--driver", required=True)
args = parser.parse_args()
binary, driver = str(Path(args.bin).resolve()), str(Path(args.driver).resolve())
checks = 0


def require(condition, message):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(message)


def saw(x):
    frac = x-x.numerator//x.denominator
    return frac-Q(1, 2) if frac else Q(0)


def energy(n):
    if not n:
        return Q(0)
    points = sorted({Q(j, r) for r in range(1, n+1) for j in range(r+1)})
    slope = n*(n+1)
    result = Q(0)
    for left, right in zip(points, points[1:]):
        middle, width = (left+right)/2, right-left
        response = 2*sum((saw(r*middle) for r in range(1, n+1)), Q(0))
        result += width*response**2 + slope**2*width**3/12
    return result


# Recover the increment from the new row/column of the energy Gram matrix,
# independently of the production divisor-weight reset formula.
increments = {n: 1-Q(1, 3)-Q(2, 3)*sum(
    (Q(gcd(r, n)**2, r*n) for r in range(1, n)), Q(0)) for n in range(1, 241)}
energies = [energy(n) for n in range(25)]
for n in range(1, 25):
    require(increments[n] == 1-energies[n]+energies[n-1], (n, "actual affine energy increment"))

# Triangular harmonic budgets, with no production imports or coprime sums.
weights, harmonic = [Q(0)]*241, Q(0)
for n in range(1, 241):
    weights[n] = (n*harmonic-sum((d**3*weights[d] for d in range(1, n)
                                 if n%d == 0), Q(0)))/n**3
    harmonic += Q(1, n)
mass = [sum(weights[:m+1], Q(0)) for m in range(241)]


def table(kind, period):
    if kind == 0:
        return [Q(0)]*period, [Q(0)]*period
    if kind == 1:
        return [Q(-2, 3)]*period, [Q(5, 7)]*period
    if kind == 2:
        return ([Q((7*j+period)%13-6, j%5+1) for j in range(period)],
                [Q((5*j+3*period)%11-5, j%7+1) for j in range(period)])
    return ([Q(j == period//2) for j in range(period)],
            [Q(-7, 4) if j == period-1 else Q(0) for j in range(period)])


def finite(length, real, imag):
    period = len(real)
    return (sum((increments[n]*real[n%period] for n in range(1, length+1)), Q(0))/length,
            -sum((increments[n]*imag[n%period] for n in range(1, length+1)), Q(0))/length)


@lru_cache(None)
def centers(real, imag):
    period = len(real)
    re, im = sum(real, Q(0))/period, sum(imag, Q(0))/period
    values = [(Q(2, 3)*re, -Q(2, 3)*im)]
    for k in range(1, 241):
        cycle = lcm(k, period)
        # Enumerate actual visits on a complete cycle. The production routine
        # instead filters residue labels by CRT compatibility.
        re -= k*weights[k]*sum((real[n%period] for n in range(0, cycle, k)), Q(0))/cycle
        im -= k*weights[k]*sum((imag[n%period] for n in range(0, cycle, k)), Q(0))/cycle
        values.append((Q(2, 3)*re, -Q(2, 3)*im))
    return values


def haar(cutoff, real, imag):
    re, im = centers(tuple(real), tuple(imag))[cutoff]
    return re, im, Q(2, 3)*max(map(abs, real))*(1-mass[cutoff]), Q(2, 3)*max(map(abs, imag))*(1-mass[cutoff])


records, enclosures = Counter(), {}
for line in subprocess.check_output([driver], text=True).splitlines():
    fields = line.split()
    kind = fields[0]
    records[kind] += 1
    if kind == "invalid-input-and-alias-checks":
        require(fields[1:] == ["PASS"], line)
        continue
    if kind == "reset":
        require(Q(fields[2]) == increments[int(fields[1])], line)
        continue
    variant, period, size = map(int, fields[1:4])
    real, imag = table(variant, period)
    actual = tuple(map(Q, fields[4:]))
    if kind == "finite":
        require(actual == finite(size, real, imag), line)
    elif kind == "haar":
        require(actual == haar(size, real, imag), line)
        enclosures[variant, period, size] = actual
    else:
        raise AssertionError("Unknown driver output: "+line)
require(records == Counter(reset=240, finite=320, haar=320,
                           **{"invalid-input-and-alias-checks": 1}), records)

for (variant, period, cutoff), (re, im, rr, ri) in enclosures.items():
    real, imag = table(variant, period)
    later_re, later_im = centers(tuple(real), tuple(imag))[240]
    require(rr >= 0 and ri >= 0, (variant, period, cutoff, "nonnegative exact radii"))
    require(abs(later_re-re) <= rr and abs(later_im-im) <= ri,
            (variant, period, cutoff, "independent later partial within enclosure"))
    if variant == 1:
        require(abs(re) <= rr and abs(im) <= ri, (period, cutoff, "constant test has zero full Haar mean"))
    earlier = [m for v, p, m in enclosures if v == variant and p == period and m < cutoff]
    if earlier:
        pr, pi, prr, pri = enclosures[variant, period, max(earlier)]
        require(pr-prr <= re-rr <= re+rr <= pr+prr and
                pi-pri <= im-ri <= im+ri <= pi+pri,
                (variant, period, cutoff, "component intervals nest"))

for n in (1, 2, 6, 24, 239, 240):
    text = subprocess.check_output([binary, "weighted-remainder-state", "reset", str(n)], text=True)
    value = next(line.split()[1] for line in text.splitlines() if line.startswith("increment "))
    require(Q(value) == increments[n], (n, "CLI increment"))

for n, period, residue, cutoff in [(1, 1, 0, 2), (6, 2, 0, 2), (24, 6, 1, 12),
                                    (1, 239, 238, 240), (240, 240, 0, 239), (239, 7, 6, 240)]:
    real, imag = [Q(j == residue) for j in range(period)], [Q(0)]*period
    text = subprocess.check_output([binary, "weighted-remainder-state", "pairing",
                                   *map(str, (n, period, residue, cutoff))], text=True)
    values = {line.rsplit(" ", 1)[0]: Q(line.rsplit(" ", 1)[1])
              for line in text.splitlines() if line.startswith(("finite average ", "Haar "))}
    center, _, radius, _ = haar(cutoff, real, imag)
    require(values == {"finite average": finite(n, real, imag)[0], "Haar center": center,
                       "Haar radius": radius, "Haar lower": center-radius, "Haar upper": center+radius},
            (n, period, residue, cutoff, "CLI pairing"))

for operands in [["reset"], ["reset", "0"], ["reset", "-1"], ["reset", "241"],
                 ["reset", "2x"], ["reset", "2", "extra"], ["pairing"],
                 ["pairing", "0", "2", "0", "2"], ["pairing", "241", "2", "0", "2"],
                 ["pairing", "6", "0", "0", "2"], ["pairing", "6", "241", "0", "2"],
                 ["pairing", "6", "2", "2", "2"], ["pairing", "6", "2", "-1", "2"],
                 ["pairing", "6", "2", "0", "1"], ["pairing", "6", "2", "0", "241"],
                 ["pairing", "6", "2", "0x", "2"], ["pairing", "6", "2", "0", "2", "extra"],
                 ["pairing", "9999999999999999999999999999999", "2", "0", "2"]]:
    result = subprocess.run([binary, "weighted-remainder-state", *operands], text=True, capture_output=True)
    require(result.returncode != 0 and "Use reset" in result.stderr, operands)

print(f"PASS: {checks} independent exact boundary-pairing and interface checks.")
print("Finite increments use energy Gram rows, with direct affine energy checked through N=24.")
print("Haar centers use complete-cycle visits; weights use triangular budgets; production uses CRT residue filtering.")
print("Complex conjugation, constant/zero/signed tables, noncoprime periods, cutoff and resource endpoints, invalid inputs and aliasing are covered.")
print("Finite evidence only; infinite containment and weak convergence are separate Lean theorems.")
