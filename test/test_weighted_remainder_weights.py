#!/usr/bin/env python3
"""Independent finite-weight oracle, including literal whole-period covariance.

The C test reference visits every residue pair over complete cycles using
repeated addition to find the period. Python builds exact expectations from
those integer samples and independently recovered triangular-budget weights.
It does not use the production gcd or Jordan variance formulas.
"""
import argparse
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
checks = cli_cases = 0


def check(condition, context):
    global checks
    checks += 1
    assert condition, context


collision = [F(0) for _ in range(241)]
h = F(0)
for k in range(2, 241):
    h += F(1, k - 1)
    collision[k] = (k * h - sum((d**3 * collision[d] for d in range(2, k)
                                if k % d == 0), F(0))) / k**3

run = subprocess.run([str(Path(args.driver).resolve())], text=True, capture_output=True)
if run.returncode:
    print(run.stderr, file=sys.stderr)
    raise SystemExit(run.returncode)
profiles, vectors, epsilons, references = {}, {}, {}, {}
observations = []
variance_records = []
deficit_records = []
edges = 0
for line in run.stdout.splitlines():
    p = line.split()
    if p[0] == "profile":
        ident, cutoff = map(int, p[1:])
        profiles[ident] = cutoff
        vectors[ident] = {}
    elif p[0] == "weight":
        vectors[int(p[1])][int(p[2])] = F(p[3])
    elif p[0] == "perturbed":
        epsilons[int(p[1])] = F(p[2])
    elif p[0] == "cycle_reference":
        k, ell, total, period = map(int, p[1:])
        check(period == lcm(k, ell), line)
        references[k, ell] = references[ell, k] = F(total, 4 * period)
    elif p[0] == "edge_checks":
        edges = int(p[1])
        check(int(p[3]) == len(profiles), line)
    elif p[0] == "variance":
        variance_records.append(p)
    elif p[0] == "perturbed_deficit":
        deficit_records.append(p)
    else:
        observations.append(p)


def raw(v, n):
    return sum((F(2, 3) * w * (n % k) for k, w in v.items()), F(0))


@lru_cache(None)
def full_deficit(n):
    # Completed remainder formula with exact omitted mass, independent of
    # production's gcd-capacity box computation.
    mass = sum(collision[2:n + 1], F(0))
    prefix = sum((collision[k] * (n % k) for k in range(2, n + 1)), F(0))
    return F(2, 3) * (prefix + n * (1 - mass))


for p in deficit_records:
    n = int(p[1])
    epsilon, original, perturbed = map(F, p[2:])
    z = F(2, 3) * (n % 2 - 2 * (n % 3) + n % 4)
    check(original == full_deficit(n) and perturbed == original + epsilon*z, p)


collision_variances = [F(0), F(0)]
for m in range(2, 241):
    cross = sum((collision[k] * references[m, k] for k in range(2, m)), F(0))
    collision_variances.append(collision_variances[-1] + F(4, 9) *
                                (collision[m]**2 * references[m, m] + 2 * collision[m] * cross))


def check_variance_bound(m, bits, finite, error, cross, upper):
    check(finite == collision_variances[m], ("finite variance", m))
    check(2**(bits - 1) < 2*m <= 2**bits, ("binary bound", m))
    check(error == F(256 * (bits + 1)**2, m), ("rational L2 error", m))
    check(cross >= 0 and cross**2 >= finite*error, ("upward square-root bound", m))
    check((cross - F(1, m*m))**2 < finite*error and (cross*m*m).denominator == 1,
          ("least upper grid point", m))
    check(upper == finite + 2*cross + error and collision_variances[240] <= upper,
          ("variance interval", m))


for p in variance_records:
    m, bits = map(int, p[1:3])
    finite, error, cross, upper = map(F, p[3:7])
    check_variance_bound(m, bits, finite, error, cross, upper)
    check(abs(F(p[7]) - finite) <= F(1, 10**16) * (1 + abs(finite)), ("floating comparison", p))
check(len(variance_records) == 239, "all variance cutoffs")


@lru_cache(None)
def variance(ident):
    v = vectors[ident]
    result = F(4, 9) * sum((a * b * references[k, ell]
                            for k, a in v.items() for ell, b in v.items()), F(0))
    # Independently form the entire observable and square it when feasible.
    period = lcm(*v) if v else 1
    if period <= 100000:
        center = sum((w * F(k - 1, 3) for k, w in v.items()), F(0))
        # One common denominator makes literal full-period sums inexpensive.
        denominator = lcm(*(w.denominator for w in v.values()), 3)
        coefficients = {k: w.numerator * (denominator // w.denominator)
                        for k, w in v.items()}
        square_sum = sum(sum(c * (2 * (n % k) - k + 1)
                             for k, c in coefficients.items())**2 for n in range(period))
        check(result == F(square_sum, 9 * denominator**2 * period), ("whole potential variance", ident))
        check(sum((raw(v, n) - center for n in range(period)), F(0)) == 0,
              ("whole potential mean", ident))
    return result


for ident, epsilon in epsilons.items():
    v, m = vectors[ident], profiles[ident]
    check(0 < abs(epsilon) < F(1, 24), ("epsilon", ident))
    expected = {k: collision[k] + epsilon * ({2: 1, 3: -2, 4: 1}.get(k, 0))
                for k in range(2, m + 1)}
    check(v == expected and all(value > 0 for value in v.values()), ("perturbed weights", ident))
    check(sum(v.values(), F(0)) == sum(collision[2:m + 1], F(0)), ("mass preserved", ident))
    check(sum((w * (k - 1) for k, w in v.items()), F(0)) ==
          sum((collision[k] * (k - 1) for k in range(2, m + 1)), F(0)),
          ("stationary age preserved", ident))
    z = [F(2, 3) * (n % 2 - 2 * (n % 3) + n % 4) for n in range(12)]
    check(sum(z, F(0)) == 0 and sum((x*x for x in z), F(0)) / 12 == F(56, 27),
          ("period twelve", ident))

for p in observations:
    kind, ident = p[0], int(p[1])
    v = vectors[ident]
    mass = sum(v.values(), F(0))
    moment = sum((k * w for k, w in v.items()), F(0))
    stationary = (moment - mass) / 3
    nonnegative = all(w >= 0 for w in v.values())
    if kind == "state":
        n = int(p[2])
        check((int(p[3]), int(p[4])) == (int(nonnegative), int(mass == 1)), p)
        expected_raw = raw(v, n)
        increment = expected_raw - raw(v, n - 1)
        # Reconstruct forcing from literal adjacent-age differences.
        forcing = mass - F(3, 2) * increment
        expected = (mass, moment, expected_raw, stationary, expected_raw - stationary,
                    forcing, increment, variance(ident), variance(ident))
        check(tuple(map(F, p[5:])) == expected, p)
        check(raw(v, -1 - n) - stationary == -(expected_raw - stationary), ("reflection", p))
        if ident in epsilons:
            base = {k: collision[k] for k in range(2, profiles[ident] + 1)}
            z = F(2, 3) * (n % 2 - 2 * (n % 3) + n % 4)
            check(expected_raw - raw(base, n) == epsilons[ident] * z, ("perturbation readout", p))
    elif kind == "energy":
        n, ok, value = int(p[2]), int(p[3]), F(p[4])
        admitted = nonnegative and mass == 1 and n >= 0
        check(ok == int(admitted), p)
        check(value == (n - raw(v, n) if admitted else F(13, 17)), p)
    elif kind == "amplitude":
        q = int(p[2])
        check(F(p[3]) == sum((w for k, w in v.items() if k % q == 0), F(0)), p)
    elif kind == "alias_center":
        check(F(p[2]) == raw(v, -13) - stationary, p)
    else:
        raise AssertionError(p)

def cli(*command):
    global cli_cases
    cli_cases += 1
    return subprocess.run([str(Path(args.bin).resolve()), "weighted-remainder-state",
                           *map(str, command)], text=True, capture_output=True)


def parse_cli(result):
    check(result.returncode == 0, result.stderr)
    fields, amplitudes = {}, {}
    for line in result.stdout.splitlines()[1:]:
        p = line.split()
        if p[0] == "amplitude":
            check(int(p[1]) not in amplitudes, line)
            amplitudes[int(p[1])] = F(p[2])
        else:
            check(len(p) == 2 and p[0] not in fields, line)
            fields[p[0]] = p[1]
    return fields, amplitudes


def check_cli_state(fields, v, address, cutoff):
    mass = sum(v.values(), F(0))
    moment = sum((k * w for k, w in v.items()), F(0))
    age, stationary = raw(v, address), (moment - mass) / 3
    increment = age - raw(v, address - 1)
    norm = F(4, 9) * sum((a * b * references[k, ell]
                          for k, a in v.items() for ell, b in v.items()), F(0))
    check(int(fields["address"]) == address and int(fields["cutoff"]) == cutoff, fields)
    nonnegative = all(w >= 0 for w in v.values())
    check(tuple(int(fields[key]) for key in ["nonnegative", "unit_mass", "admissible_probability_mass"]) ==
          (int(nonnegative), int(mass == 1), int(nonnegative and mass == 1)), fields)
    names = ["mass", "first_moment", "raw_age", "stationary_age", "centered_age",
             "divisor_forcing", "finite_increment", "gram_variance", "jordan_variance"]
    check(tuple(F(fields[key]) for key in names) ==
          (mass, moment, age, stationary, age - stationary, mass - F(3, 2) * increment,
           increment, norm, norm), fields)


if args.bin:
    for m in [2, 3, 12, 239, 240]:
        fields, amplitudes = parse_cli(cli("variance", m))
        check(not amplitudes and int(fields["cutoff"]) == m and
              int(fields["cross_grid_denominator"]) == m*m, fields)
        check_variance_bound(m, int(fields["binary_exponent"]), F(fields["finite_variance"]),
                             F(fields["potential_error_squared_upper"]), F(fields["cross_upper"]),
                             F(fields["full_variance_upper"]))
        check(int(fields["cutoff_cylinder_modulus"]) == lcm(*range(1, m + 1)) and
              F(fields["cutoff_cylinder_error_squared_upper"]) == F(fields["potential_error_squared_upper"]),
              fields)
    vectors_cli = [{}, *({k: F(1)} for k in [2, 3, 12, 239, 240]),
                   {2: F(-1), 3: F(2)}, {4: F(1, 7), 6: F(6, 7)},
                   {239: F(2, 5), 240: F(3, 5)}, {2: F(2**130 + 1, 2**131)}]
    for v in vectors_cli:
        cutoff = max(v, default=2)
        for address in [0, 1, -1, "+6", 10**60, -(10**60)]:
            fields, amplitudes = parse_cli(cli("finite-weights", address,
                                               *(f"{k}:{value}" for k, value in v.items())))
            n = int(address)
            check_cli_state(fields, v, n, cutoff)
            expected_amp = {q: sum((value for k, value in v.items() if k % q == 0), F(0))
                            for q in range(2, cutoff + 1)}
            check(amplitudes == {q: value for q, value in expected_amp.items() if value}, fields)
            admitted = n >= 0 and all(value >= 0 for value in v.values()) and sum(v.values(), F(0)) == 1
            check(int(fields["unit_energy_available"]) == int(admitted), fields)
            if admitted:
                check(F(fields["unit_energy"]) == n - raw(v, n), fields)
            else:
                check("unit_energy" not in fields, fields)
    for m in [4, 12, 240]:
        for epsilon in [F(1, 48), F(-1, 48), F(1, 25), F(-1, 25)]:
            v = {k: collision[k] + epsilon * {2: 1, 3: -2, 4: 1}.get(k, 0)
                 for k in range(2, m + 1)}
            for n in [0, 6, -1, 10**60]:
                fields, amplitudes = parse_cli(cli("perturbation", m, n, epsilon))
                check(not amplitudes, fields)
                check_cli_state(fields, v, n, m)
                z = F(2, 3) * (n % 2 - 2 * (n % 3) + n % 4)
                check(F(fields["epsilon"]) == epsilon and
                      tuple(F(fields[key]) for key in ["weight_two", "weight_three", "weight_four"]) ==
                      tuple(v[k] for k in [2, 3, 4]), fields)
                check(F(fields["mass_change"]) == F(fields["stationary_age_change"]) ==
                      F(fields["change_identity_error"]) == 0, fields)
                check(F(fields["centered_age_change"]) == epsilon * z and
                      F(fields["perturbation_value"]) == z and
                      F(fields["perturbation_norm_sq"]) == F(56, 27), fields)
                check(F(fields["omitted_mass"]) == 1 - sum(collision[2:m + 1], F(0)), fields)
                if n >= 0:
                    check(F(fields["full_deficit_change"]) == epsilon * z, fields)
                else:
                    check("full_deficit_change" not in fields, fields)
                if 0 <= n <= 240:
                    check(F(fields["original_full_deficit"]) == full_deficit(n) and
                          F(fields["perturbed_full_deficit"]) == full_deficit(n) + epsilon*z, fields)
                else:
                    check("original_full_deficit" not in fields and "perturbed_full_deficit" not in fields, fields)
    invalid = []
    for token in ["", "1", "-", "+", "1/0", "1/-2", "1/+2", "1/2/3", "1e3", "nan", " 1", "1 "]:
        if token != "1":
            invalid.append(("finite-weights", 0, "2:" + token))
        invalid.append(("perturbation", 4, 0, token))
    for token in ["0:1", "1:1", "241:1", "-2:1", "+2:1", "2x:1", " 2:1", "2", "2:1:2"]:
        invalid.append(("finite-weights", 0, token))
    invalid.extend([("finite-weights", 0, "2:1/2", "2:1/2"),
                    ("finite-weights",), ("perturbation", 4, 0),
                    ("perturbation", 4, 0, "1/48", "extra")])
    for m in [0, 1, 2, 3, 241, -4, "+4", "4x", 2**80]:
        invalid.append(("perturbation", m, 0, "1/48"))
        if m not in [2, 3]:
            invalid.append(("variance", m))
    invalid.extend([("variance",), ("variance", 2, "extra")])
    for epsilon in ["0", "1/24", "-1/24", "1/23", "-1/23"]:
        invalid.append(("perturbation", 4, 0, epsilon))
    for address in ["", "-", "+", "0x1", "1/2", " 1", "1 "]:
        invalid.extend([("finite-weights", address, "2:1"),
                        ("perturbation", 4, address, "1/48")])
    for command in invalid:
        result = cli(*command)
        check(result.returncode != 0 and not result.stdout, (command, result))

print(f"finite-weight oracle PASS: checks={checks + edges}; profiles={len(profiles)}; "
      f"records={len(observations) + len(variance_records) + len(deficit_records)}; C edge checks={edges}; CLI cases={cli_cases}")
print("Literal full-period covariance reference for every pair 2..240; whole potential "
      "squares where admitted; exact supplied mass, signed weights, reset differences, "
      "unit-mass energies, finite amplitudes and perturbed collision families passed.")
print("Finite systems only; the infinite general-weight criterion and perturbed Haar "
      "potential are separate Lean theorems.")
