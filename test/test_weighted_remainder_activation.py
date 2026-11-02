#!/usr/bin/env python3
"""Independent integer/Fraction oracle; imports no implementation code.

Direct cube masses use a common integer denominator. The activation law
is checked a second way by enumerating the three outcomes inactive,
active-and-zero and active-and-one. Conditional antichains are counted by
literal submask enumeration, not the production subset zeta transform.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
from math import comb, prod
from pathlib import Path
import random
import subprocess
import sys


def run(args, **kwargs):
    result = subprocess.run([str(x) for x in args], text=True, capture_output=True, **kwargs)
    if result.returncode:
        sys.stderr.write(result.stderr)
        result.check_returncode()
    return result


def parse(text):
    return dict(line.split("=", 1) for line in text.splitlines() if "=" in line)


def oracle(b, values, a, u, v):
    n = len(b)
    chosen = {s for s, f in enumerate(values) if u <= f <= v}
    den = prod(p.denominator for p in b)
    pairs = [(p.denominator-p.numerator, p.numerator) for p in b]
    masses = [prod(pairs[i][(s >> i) & 1] for i in range(n)) for s in range(1 << n)]
    assert sum(masses) == den
    expected_count = Q(sum(s.bit_count()*m for s, m in enumerate(masses)), den)
    probability = Q(sum(masses[s] for s in chosen), den)
    coupled = 0
    # A ternary outcome has probabilities (1-2b_i, b_i, b_i).
    triples = [(p.denominator-2*p.numerator, p.numerator, p.numerator) for p in b]
    for state in product(range(3), repeat=n):
        s = sum(1 << i for i, x in enumerate(state) if x == 2)
        if s in chosen:
            coupled += prod(triples[i][x] for i, x in enumerate(state))
    assert Q(coupled, den) == probability
    active_pairs = [(p.denominator-2*p.numerator, 2*p.numerator) for p in b]
    first = second = 0
    sperner = Q(0)
    for active in range(1 << n):
        k = active.bit_count()
        m = prod(active_pairs[i][(active >> i) & 1] for i in range(n))
        first += k*m
        second += k*k*m
        count = 0
        sub = active
        while True:
            count += sub in chosen
            if not sub:
                break
            sub = (sub-1) & active
        assert count <= comb(k, k//2)
        if active in chosen:
            assert count == 1
        sperner += Q(m*comb(k, k//2), den*(1 << k))
    mean = Q(first, den)
    variance = Q(second, den)-mean*mean
    edge_min = min((values[s | (1 << i)]-values[s]
                    for s in range(1 << n) for i in range(n) if not s & (1 << i)),
                   default=None)
    assert a > 0 and v-u < a and (edge_min is None or edge_min >= a)
    assert probability <= sperner <= 1
    bound = 400/(1+expected_count)
    assert probability**2 <= bound
    return {"dimension": n, "cube_size": 1 << n, "interval_count": len(chosen),
            "interval_antichain": 1,
            "minimum_increment": "undefined_no_edges" if edge_min is None else edge_min,
            "probability_sum": expected_count, "event_probability": probability,
            "coupled_probability": Q(coupled, den), "active_mean": mean,
            "active_variance": variance, "sperner_bound": sperner,
            "universal_bound_squared": bound}


def command(b, f, a, u, v):
    return " ".join(["activation", str(len(b)), str(a), str(u), str(v),
                     ",".join(map(str, b)) or "-", ",".join(map(str, f))])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--driver", required=True)
    parser.add_argument("--bin")
    args = parser.parse_args()
    driver = Path(args.driver).resolve()
    cases = []

    def add(b, f, a, u, v):
        cases.append((command(b, f, a, u, v), oracle(b, f, a, u, v)))

    # All triples of biases through dimension four, every rank interval.
    for n in range(5):
        f = [Q(s.bit_count()) for s in range(1 << n)]
        for b in product([Q(0), Q(1, 4), Q(1, 2)], repeat=n):
            for rank in range(n+1):
                add(b, f, Q(1), Q(rank), Q(rank))
    rng = random.Random(260911)
    for n in range(1, 10):
        for sample in range(5):
            b = [Q(rng.randrange(8), 17) for _ in range(n)]
            w = [Q(rng.randrange(3, 10), 3) for _ in range(n)]
            cross = {(i, j): Q(rng.randrange(5), 7) for i in range(n) for j in range(i)}
            f = [Q(-7, 3) + sum((w[i] for i in range(n) if s & (1 << i)), Q(0)) +
                 sum((c for (i, j), c in cross.items() if s & (1 << i) and s & (1 << j)), Q(0))
                 for s in range(1 << n)]
            u = f[rng.randrange(1 << n)]
            add(b, f, Q(1), u, u+Q(1, 2))
            if sample == 0:
                add(b, f, Q(1), u+1, u)  # empty interval
    for n in [10, 11, 12]:
        f = [Q(s.bit_count()) for s in range(1 << n)]
        add([Q(1, 2)]*n, f, Q(1), Q(n//2), Q(n//2))
        add([Q(i, 2*n) for i in range(n)], f, Q(1), Q(n//2), Q(n//2))
    huge = Q(10**100+3, 10**80+7)
    add([Q(1, 10**100+9), Q(1, 2)], [-huge, Q(0), Q(0), huge], huge, Q(0), Q(0))
    add([], [Q(-5, 3)], Q(1, 101), Q(-5, 3), Q(-5, 3))
    add([], [Q(0)], Q(1), Q(1), Q(0))
    invalid = [
        "activation 13 1 0 0 - 0", "activation 999999999999999999999 1 0 0 - 0",
        "activation -1 1 0 0 - 0", "activation 2x 1 0 0 - 0",
        "activation 1 0 0 0 1/2 0,1", "activation 1 -1 0 0 1/2 0,1",
        "activation 1 1 0 1 1/2 0,1", "activation 1 1 0 2 1/2 0,1",
        "activation 1 1 0 0 1/0 0,1", "activation 1 1 0 0 -1/2 0,1",
        "activation 1 1 0 0 2/3 0,1", "activation 1 1 0 0 0 0,0",
        "activation 2 1 0 0 1/2 0,1,1,2", "activation 1 1 0 0 1/2,1/3 0,1",
        "activation 1 1 0 0 1/2 0", "activation 1 1 0 0 1/2 0,1,2",
        "activation 1 1 0 0 1/2, 0,1", "activation 2 1 0 0 1/2,,1/3 0,1,1,2",
        "activation 1 1 0 0 1/-2 0,1", "activation 1 1 0 0 0.5 0,1",
        "activation 1 1 0 0 1/2 0,1/0", "activation 0 1 0 0 0 0",
        "activation 0 1 0 0 - 0 extra", "activation 0 1 0 0 -",
    ]
    stream = "\n".join([c for c, _ in cases]+invalid)+"\n"
    output = run([driver, "--stream"], input=stream)
    records = [parse(block) for block in output.stdout.split("BEGIN\n")[1:]]
    assert len(records) == len(cases)+len(invalid)
    checks = 0
    for (cmd, expected), actual in zip(cases, records):
        assert actual.pop("exit") == "0", (cmd, actual)
        for key, value in expected.items():
            assert actual[key] == str(value), (cmd, key, actual[key], value)
            checks += 1
    for actual in records[len(cases):]:
        assert actual == {"exit": "1"}, actual
        checks += 1
    api = int(parse(run([driver, "--self-test"]).stdout)["api_checks"])
    checks += api
    cli = 0
    if args.bin:
        binary = Path(args.bin).resolve()
        for index in [0, 1, 4, len(cases)//2, len(cases)-5, len(cases)-3, len(cases)-2, len(cases)-1]:
            cmd, expected = cases[index]
            actual = parse(run([binary, "weighted-remainder-state", *cmd.split()]).stdout)
            assert actual == {k: str(v) for k, v in expected.items()}, (cmd, actual)
            cli += 1
        for cmd in invalid:
            r = subprocess.run([str(binary), "weighted-remainder-state", *cmd.split()],
                               text=True, capture_output=True)
            assert r.returncode != 0 and "Invalid activation query" in r.stderr, (cmd, r)
            cli += 1
        checks += cli
    print(f"activation independent checks={checks}; queries={len(records)}; api_edges={api}; cli_cases={cli}")
    print("PASS: exact common-denominator cube law, independent ternary coupling, literal antichain enumeration,")
    print("conditional Sperner bounds, active-count distribution moments, invalid domains and aliases.")
    print("Finite dimensions 0..12. Universal Bernoulli activation is a separate Lean theorem.")


if __name__ == "__main__":
    main()
