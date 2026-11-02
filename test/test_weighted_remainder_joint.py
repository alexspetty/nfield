"""Independent complete-period and boundary-energy oracle for joint APIs."""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--driver", required=True)
parser.add_argument("--bin")
args = parser.parse_args()
driver = str(Path(args.driver).resolve())
checks = 0


def require(condition, message):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(message)


# Each new row of the actual gcd energy Gram matrix determines g(n),
# independently of the production divisor forcing and its selected weights.
energy = [Q(0)]
increments = [Q(0)]
for n in range(1, 241):
    change = Q(1, 3) + Q(2, 3)*sum((Q(gcd(n, j)**2, n*j)
                                   for j in range(1, n)), Q(0))
    energy.append(energy[-1]+change)
    increments.append(1-change)
forcing = [1-Q(3, 2)*g for g in increments]
deficits = [Q(n)-energy[n] for n in range(241)]

# A triangular harmonic-budget inversion, without production coprime sums.
weights, harmonic = [Q(0)]*241, Q(0)
for n in range(1, 241):
    weights[n] = (n*harmonic-sum((d**3*weights[d] for d in range(1, n)
                                 if n%d == 0), Q(0)))/n**3
    harmonic += Q(1, n)

requests, expected = [], []


def add(query, answer):
    requests.append(query)
    expected.append(answer)


def crt(periods, shifts, known_address=None):
    modulus = lcm(*periods)
    if known_address is None:
        # Actual complete-cycle visits; no generalized CRT inverse algorithm.
        hits = [n for n in range(modulus)
                if all((n+h)%k == 0 for k, h in zip(periods, shifts))]
        require(len(hits) <= 1, (periods, shifts, "complete cycle multiplicity"))
        residue = hits[0] if hits else 0
        probability = Q(len(hits), modulus)
    else:
        residue, probability = known_address % modulus, Q(1, modulus)
    add("C "+str(len(periods))+" "+" ".join(f"{k} {h}" for k, h in zip(periods, shifts)),
        ("C", probability, residue, modulus, tuple(periods), tuple(shifts)))


crt([], [])
for k in range(2, 15):
    for h in [0, 1, k-1, 240]:
        crt([k], [h])
for k, m in product(range(2, 15), repeat=2):
    for a, b in product([0, 1, 7, 240], repeat=2):
        crt([k, m], [a, b])
for periods in [(2, 4, 6), (4, 6, 9), (6, 10, 15), (4, 8, 16),
                (7, 11, 13), (12, 18, 30), (2, 3, 5, 7),
                (2, 3, 4, 5, 6, 7, 8, 9), (240, 120, 60, 30, 15, 10, 6, 2)]:
    for seed in range(12):
        crt(periods, [(seed*(i+1)+i*i)%241 for i in range(len(periods))])
    crt(periods, [(-137)%k for k in periods])
    crt(periods, [0]*len(periods))
large = (239, 233, 229, 227, 223, 211, 199, 197)
require(lcm(*large) > 2**53, "large exact CRT period exceeds floating integer precision")
for address in [0, 1, 12345678901234567890123]:
    crt(large, [(-address)%k for k in large], address)

for n in range(1, 241):
    add(f"F {n}", ("F", forcing[n]))
for start in range(241):
    for length in sorted({0, 240-start, *[j for j in [1, 2, 7, 31] if j <= 240-start]}):
        add(f"B {start} {length}", ("B", deficits[start+length]-deficits[start]))

for length in [1, 2, 6, 12, 31, 120, 239, 240]:
    maximum = 240-length
    cases = [([], []), ([0], [0]), ([0], [1]), ([0], [2]), ([0], [16]),
             ([maximum], [1]), ([0, maximum], [1, 1]), ([0, maximum], [3, 5])]
    for dimension in [3, 4, 8]:
        shifts = [(3*i*i+7*i) % (maximum+1) for i in range(dimension)]
        cases += [(shifts, [1]*dimension), (shifts, [2]*dimension)]
    for kind in [0, 1]:
        values = increments if kind else forcing
        for shifts, powers in cases:
            answer = sum((prod(values[n+h]**p for h, p in zip(shifts, powers))
                          for n in range(1, length+1)), Q(0))/length
            add(f"M {length} {kind} {len(shifts)} "+
                " ".join(f"{h} {p}" for h, p in zip(shifts, powers)), ("M", answer))


@lru_cache(None)
def cutoff_cycle(cutoff):
    period = lcm(*range(2, cutoff+1))
    values = [sum((k*weights[k] for k in range(2, cutoff+1) if n%k == 0), Q(0))
              for n in range(period)]
    return period, values


for cutoff in range(2, 13):
    cycle, values = cutoff_cycle(cutoff)
    for dimension in range(9):
        if (cutoff-1)**dimension > 65536:
            continue
        lists = [[0]*dimension, [(i*i+3*i+239)%241 for i in range(dimension)]]
        for shifts in lists:
            answer = sum((prod(values[(n+h)%cycle] for h in shifts)
                          for n in range(cycle)), Q(0))/cycle
            add(f"H {cutoff} {dimension} "+" ".join(map(str, shifts)), ("H", answer))
for cutoff in [31, 120, 239, 240]:
    for shift in [0, 1, 239, 240]:
        add(f"H {cutoff} 1 {shift}", ("H", sum(weights[:cutoff+1], Q(0))))
    add(f"H {cutoff} 0", ("H", Q(1)))

edge = subprocess.run([driver, "--edges"], text=True, capture_output=True, check=True)
require(edge.stdout.strip() == "API_EDGE_CHECKS=36", edge.stdout)
run = subprocess.run([driver], input="\n".join(requests)+"\n", text=True,
                     capture_output=True, check=True)
lines = run.stdout.splitlines()
require(len(lines) == len(expected), (len(lines), len(expected), run.stderr))
for query, line, answer in zip(requests, lines, expected):
    parts = line.split()
    require(parts[0] == answer[0], (query, line))
    require(Q(parts[1]) == answer[1], (query, line, answer[:4]))
    if parts[0] == "C":
        residue, modulus = int(parts[2]), int(parts[3])
        require((residue, modulus) == (answer[2], answer[3]), (query, line, answer[:4]))
        require(0 <= residue < modulus, (query, "canonical residue"))
        if answer[1]:
            require(all((residue+h)%k == 0 for k, h in zip(answer[4], answer[5])),
                    (query, "every congruence"))

if args.bin:
    binary = str(Path(args.bin).resolve())

    def cli(*words, valid=True):
        result = subprocess.run([binary, "weighted-remainder-state", *map(str, words)],
                                text=True, capture_output=True)
        require((result.returncode == 0) == valid, (words, result.returncode, result.stderr))
        return dict(line.split("=", 1) for line in result.stdout.splitlines() if "=" in line)

    require(Q(cli("forcing", 240)["full_reset_forcing"]) == forcing[240], "CLI forcing")
    require(Q(cli("block", 31, 209)["deficit_difference"]) == deficits[240]-deficits[31], "CLI block")
    require(Q(cli("moment", 6, "g", "0:1", "1:2")["finite_moment"]) ==
            sum((increments[n]*increments[n+1]**2 for n in range(1, 7)), Q(0))/6, "CLI moment")
    require(Q(cli("haar-moment", 4, 0, 1)["finite_haar_reset_moment"]) ==
            sum((cutoff_cycle(4)[1][n]*cutoff_cycle(4)[1][(n+1)%12] for n in range(12)), Q(0))/12,
            "CLI Haar moment")
    require(cli("crt", "4:0", "6:1")["compatible"] == "0", "CLI incompatibility")
    require(cli("crt")["haar_probability"] == "1", "CLI empty list")
    for words in [("forcing", 0), ("forcing", "-1"), ("forcing", 241),
                  ("block", 240, 1), ("block", 0), ("moment", 0, "g"),
                  ("moment", 1, "x"), ("moment", 1, "g", "240:1"),
                  ("moment", 1, "g", "0:17"), ("moment", 1, "g", "0:16", "1:1"),
                  ("haar-moment", 6, 0, 0, 0, 0, 0, 0, 0),
                  ("crt", "1:0"), ("crt", "2:"), ("crt", ":0"),
                  ("crt", "2:0:1"), ("crt", "2:1.0"), ("crt", "2:-1"),
                  ("crt", "0000000000000000000002:0"),
                  ("crt", *["2:0"]*9)]:
        cli(*words, valid=False)

print(f"JOINT_ORACLE_PASS checks={checks} queries={len(requests)} api_edges=36 cli={bool(args.bin)}")
print("Complete-period CRT/cutoff oracle; independent energy-derived integer moments; exact rationals.")
print("Finite admitted domains only; the infinite joint-law theorem is separate Lean evidence.")
