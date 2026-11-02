"""Independent exact clock, cycle-law and complete-period covariance oracle.

Weights are recovered from triangular harmonic budgets, independently of
production's coprime harmonic sums. Cesaro counts enumerate small windows;
total variation sums every residue discrepancy, independently of the C
closed formula. Finite laws and covariance visit complete lcm periods.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import lcm
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser()
parser.add_argument("--driver", required=True)
parser.add_argument("--bin")
args = parser.parse_args()
checks = records = cli_cases = 0


def check(condition, context):
    global checks
    checks += 1
    assert condition, context


weights = [F(0) for _ in range(241)]
harmonic = F(0)
for k in range(2, 241):
    harmonic += F(1, k - 1)
    weights[k] = (k * harmonic - sum((d**3 * weights[d]
                 for d in range(2, k) if k % d == 0), F(0))) / k**3


@lru_cache(None)
def clock(m, a):
    mass = sum(weights[2:m + 1], F(0))
    raw = sum((F(2, 3) * weights[k] * (a % k) for k in range(2, m + 1)), F(0))
    stationary = sum((weights[k] * F(k - 1, 3) for k in range(2, m + 1)), F(0))
    previous = sum((F(2, 3) * weights[k] * ((a - 1) % k)
                    for k in range(2, m + 1)), F(0))
    return mass, 1 - mass, raw, stationary, raw - stationary, raw - previous


@lru_cache(None)
def counts(k, last):
    if last <= 100:
        visits = Counter(n % k for n in range(last + 1))
        return tuple(visits[r] for r in range(k))
    return tuple((last - r) // k + 1 if last >= r else 0 for r in range(k))


@lru_cache(None)
def tv_prefix(last):
    prefix = [F(0), F(0)]
    for k in range(2, 241):
        distance = weights[k] * sum((abs(F(n, last + 1) - F(1, k))
                                     for n in counts(k, last)), F(0)) / 2
        prefix.append(prefix[-1] + distance)
    return prefix


@lru_cache(None)
def covariance(k, ell):
    period = lcm(k, ell)
    # Visit every actual pair; no gcd covariance formula is used here.
    numerator = sum((2 * (n % k) - k + 1) * (2 * (n % ell) - ell + 1)
                    for n in range(period))
    return F(numerator, 4 * period)


def floating_close(text, reference):
    # A comparison tolerance, not a rounding enclosure for the public API.
    return abs(F(text) - reference) <= F(1, 10**16) * (1 + abs(reference))


run = subprocess.run([str(Path(args.driver).resolve())], text=True, capture_output=True)
if run.returncode:
    print(run.stderr, file=sys.stderr)
    raise SystemExit(run.returncode)
laws = {}
law_meta = {}
edges = 0
tv_seen = {}
for line in run.stdout.splitlines():
    p = line.split()
    kind = p[0]
    if kind == "edge_checks":
        edges = int(p[1])
        check(edges > 0, line)
        continue
    records += 1
    if kind == "clock":
        m, a = map(int, p[1:3])
        got = tuple(map(F, p[3:]))
        check(got == clock(m, a), line)
        check(got[0] + got[1] == 1 and got[4] == got[2] - got[3], line)
        check(got[4] == -clock(m, -1 - a)[4], ("reflection", line))
    elif kind == "floating":
        m, a = map(int, p[1:3])
        reference = clock(m, a)
        check(all(floating_close(s, reference[i]) for s, i in zip(p[3:], [0, 3, 4, 5])), line)
    elif kind == "cycle":
        k, r, a, last = map(int, p[1:5])
        orbit, stationary, average = map(F, p[5:])
        check(orbit == (weights[k] if a % k == r else 0), line)
        check(stationary == weights[k] / k, line)
        check(average == weights[k] * F(counts(k, last)[r], last + 1), line)
        check(counts(k, last)[r] >= 0 and sum(counts(k, last)) == last + 1, line)
    elif kind == "tv":
        m, last = map(int, p[1:3])
        lower, upper, tail = map(F, p[3:])
        check(lower == tv_prefix(last)[m], line)
        check(tail == 1 - sum(weights[2:m + 1], F(0)), line)
        check(upper == lower + tail and 0 <= lower <= upper <= 1, line)
        if (m - 1, last) in tv_seen:
            previous = tv_seen[m - 1, last]
            check(previous[0] <= lower <= upper <= previous[1], ("nested", line))
        tv_seen[m, last] = lower, upper
    elif kind == "atom":
        m, value, count = int(p[1]), F(p[2]), int(p[3])
        table = laws.setdefault(m, {})
        check(value not in table and count > 0, line)
        if table:
            check(next(reversed(table)) < value, ("ordered", line))
        table[value] = count
    elif kind == "law":
        m, period, distinct = map(int, p[1:])
        law_meta[m] = period, distinct
    elif kind == "covariance":
        k, ell = map(int, p[1:3])
        value = F(p[3])
        check(value == covariance(k, ell), line)
        check(floating_close(p[4], value), line)
    elif kind == "budget":
        m = int(p[1])
        # Literal cross pairs and direct weighted periods, without a Mobius transform.
        harmonic_cross = sum((F(1, i * j) for j in range(1, m + 1)
                              for i in range(1, j)), F(0))
        first_moment = sum((k * weights[k] for k in range(2, m + 1)), F(0))
        check(F(p[2]) == harmonic_cross and F(p[3]) == first_moment, line)
    else:
        raise AssertionError(line)

for m in range(2, 13):
    period = lcm(*range(1, m + 1))
    # This is the actual whole-period distribution, including equal values.
    expected = Counter(sum((weights[k] * F(2 * (n % k) - k + 1, 3)
                           for k in range(2, m + 1)), F(0)) for n in range(period))
    check(laws[m] == expected, ("complete law", m))
    check(law_meta[m] == (period, len(expected)), ("law counts", m))
    check(sum(expected.values()) == period, ("law normalization", m))
    check(sum((value * count for value, count in expected.items()), F(0)) == 0,
          ("law mean", m))
    check(all(expected[value] == expected[-value] for value in expected), ("law reflection", m))

def cli(*command):
    global cli_cases
    cli_cases += 1
    return subprocess.run([str(Path(args.bin).resolve()), "weighted-remainder-state",
                           *map(str, command)], text=True, capture_output=True)


def rows(result):
    check(result.returncode == 0, result.stderr)
    return dict(line.split(maxsplit=1) for line in result.stdout.splitlines()[1:])


if args.bin:
    fields = ["retained_mass", "omitted_mass", "raw_age", "stationary_age",
              "centered_age", "finite_increment"]
    for m in [2, 3, 12, 60, 240]:
        for a in [0, -1, "+17", 2**200, -(2**200)]:
            got = rows(cli("clock", m, a))
            check(int(got["cutoff"]) == m and int(got["address"]) == int(a), got)
            check(tuple(F(got[key]) for key in fields) == clock(m, int(a)), got)
    for m in range(2, 13):
        result = cli("clock-law", m)
        check(result.returncode == 0, result.stderr)
        got = {}
        metadata = {}
        for line in result.stdout.splitlines():
            p = line.split()
            if p[0] == "atom":
                value, count = F(p[1]), int(p[2])
                check(value not in got, line)
                got[value] = count
            elif p[0] in ["period", "distinct", "cutoff", "retained_mass", "omitted_mass"]:
                metadata[p[0]] = F(p[1])
        check(got == laws[m], ("CLI finite law", m))
        check(metadata["period"] == law_meta[m][0] and
              metadata["distinct"] == len(got) and metadata["cutoff"] == m, metadata)
        check((metadata["retained_mass"], metadata["omitted_mass"]) == clock(m, 0)[:2], metadata)
    for k in [2, 3, 7, 12, 239, 240]:
        for r in [0, k - 1]:
            for last in [0, k - 2, k - 1, 10**50]:
                for a in [-1, 0]:
                    got = rows(cli("cycle", k, r, a, last))
                    check((int(got["period"]), int(got["residue"]), int(got["next_residue"])) ==
                          (k, r, (r + 1) % k), got)
                    check(int(got["address"]) == a and int(got["last_observation"]) == last and
                          int(got["observations"]) == last + 1, got)
                    check(F(got["orbit_mass"]) == (weights[k] if a % k == r else 0), got)
                    check(F(got["stationary_mass"]) == weights[k] / k and
                          F(got["cesaro_mass"]) == weights[k] * F(counts(k, last)[r], last + 1), got)
                    check(F(got["cycle_mass"]) == weights[k] and
                          F(got["other_cycle_mass"]) == 1 - weights[k], got)
    for m in [2, 3, 12, 240]:
        for last in [0, 1, 6, 100, 10**50]:
            got = rows(cli("cycle-tv", m, last))
            lower, tail = tv_prefix(last)[m], clock(m, 0)[1]
            check(int(got["last_observation"]) == last and int(got["observations"]) == last + 1, got)
            check(tuple(F(got[key]) for key in ["tv_lower", "tv_upper", "omitted_mass"]) ==
                  (lower, lower + tail, tail), got)
    for k, ell in [(1, 240), (12, 18), (239, 240), (240, 240)]:
        got = rows(cli("covariance", k, ell))
        check(int(got["first_period"]) == k and int(got["second_period"]) == ell and
              F(got["covariance"]) == covariance(k, ell), got)
    for m in [0, 1, 2, 3, 12, 239, 240]:
        got = rows(cli("age-budget", m))
        expected_cross = sum((F(1, i * j) for j in range(1, m + 1)
                              for i in range(1, j)), F(0))
        check(int(got["cutoff"]) == m and F(got["harmonic_cross_sum"]) == expected_cross, got)
        check(F(got["first_moment_mobius"]) ==
              sum((k * weights[k] for k in range(2, m + 1)), F(0)), got)

    invalid = []
    for m in [0, 1, 241, -2, "+2", " 2", "2x", "", 2**80]:
        invalid.extend([("clock", m, 0), ("clock-law", m),
                        ("cycle", m, 0, 0, 0), ("cycle-tv", m, 0)])
    invalid.extend(("clock-law", m) for m in [13, 14, 239, 240])
    for text in ["", "+", "-", " 1", "1 ", "1x", "1.0", "0x10", "1e9"]:
        invalid.extend([("clock", 2, text), ("cycle", 2, 0, text, 0),
                        ("cycle", 2, 0, 0, text), ("cycle-tv", 2, text)])
    for r in [-1, 2, 240, "+0", "0x0", " 0"]:
        invalid.append(("cycle", 2, r, 0, 0))
    invalid.extend([("cycle", 2, 0, 0, -1), ("cycle-tv", 2, -1)])
    for k in [0, 241, -1, "+1", "1x", 2**80]:
        invalid.extend([("covariance", k, 2), ("covariance", 2, k)])
        if k != 0:
            invalid.append(("age-budget", k))
    for command in [("clock", 2, 0), ("clock-law", 2), ("cycle", 2, 0, 0, 0),
                    ("cycle-tv", 2, 0), ("covariance", 2, 2), ("age-budget", 2)]:
        invalid.extend([command[:-1], (*command, "extra")])
    for command in invalid:
        result = cli(*command)
        check(result.returncode != 0 and not result.stdout, (command, result))

print(f"clock oracle PASS: checks={checks + edges}; records={records}; "
      f"C edge checks={edges}; CLI cases={cli_cases}")
print("Triangular weights, exact signed clocks, literal prefix cycle counts, "
      "every-residue total variation, whole-period laws and covariance, "
      "floating API comparisons, invalid domains and GMP aliases passed.")
print("Finite cutoffs only. No point value of the limiting Haar potential is assigned.")
