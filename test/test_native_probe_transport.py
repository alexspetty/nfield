"""Independent Decimal projections for the fourfold probe transport identity."""
import argparse
import json
import subprocess
from decimal import Decimal as D
from pathlib import Path
import test_native_detector as ref


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bin', required=True)
    binary = str(Path(parser.parse_args().bin).resolve())
    for N in (2, 3, 4, 7, 8):
        args = [binary, 'native-refinement', 'probe-transport', str(N), '--json']
        process = subprocess.run(args, check=True, capture_output=True, text=True, timeout=180)
        ref.check(not process.stderr, process.stderr)
        actual = json.loads(process.stdout)
        top = 16*N
        mean = {j: D(j).ln()/j for j in range(2, top+1)}

        def dot(a, b):
            return sum((v*b.get(j, D()) for j, v in a.items()), D())

        def pair(a, b):
            return sum((v*w*ref.gram(j, k) for j, v in a.items() for k, w in b.items()), D())

        def project(cutoff, rhs):
            clocks = list(range(2, cutoff+1))
            solution = ref.solve([[ref.gram(j, k) for k in clocks] for j in clocks],
                                 [rhs[j] for j in clocks])
            return dict(zip(clocks, solution))

        def difference(a, b):
            return {j: a.get(j, D())-b.get(j, D()) for j in a.keys() | b.keys()}

        def lift(a, scale):
            result = {}
            for j, value in a.items():
                result[scale*j] = result.get(scale*j, D())+D(scale).sqrt()*value
                result[scale] = result.get(scale, D())-D(scale).sqrt()*value/j
            return result

        def probe(cutoff, depth):
            scale = 2**depth
            M = cutoff//scale
            rhs = {j: D(2).sqrt()/(2*j) for j in range(2, 4*M+1)}
            detail = difference(project(4*M, rhs), project(M, rhs))
            raw = detail if scale == 1 else lift(detail, scale)
            coupling = {j: sum((v*ref.gram(j, k) for k, v in raw.items()), D())
                        for j in range(2, cutoff+1)}
            return difference(raw, project(cutoff, coupling))

        p, q = project(N, mean), project(4*N, mean)
        residual, next_residual = 1-dot(p, mean), 1-dot(q, mean)
        H = Hnext = 0
        while 2**H*residual < 4:
            H += 1
        while 2**Hnext*next_residual < 4:
            Hnext += 1
        depths = [h for h in range(H) if N//(2**h) >= 2 and h+2 < Hnext]
        ref.check(actual['schema'] == 'nfield.native-probe-transport.v1', 'schema')
        ref.check(actual['cutoff'] == N and actual['next_cutoff'] == 4*N and actual['fine_cutoff'] == top, 'cutoffs')
        ref.check(actual['observation_truncation'] is False and actual['failures'] == 0, 'complete native norm')
        ref.check(actual['paired_depths'] == len(depths) and actual['shallow_horizon'] == H and actual['next_shallow_horizon'] == Hnext, 'paired eligibility')
        ref.contains(actual['residual'], residual, 'old residual')
        ref.contains(actual['next_residual'], next_residual, 'new residual')
        old, new, removed = [], [], []
        for row, h in zip(actual['probes'], depths):
            a, b = probe(N, h), probe(4*N, h+2)
            copied = lift(a, 4)
            correction = project(4*N, {j: pair({j: D(1)}, copied) for j in range(2, 4*N+1)})
            ref.check(row['depth'] == h and row['next_depth'] == h+2 and row['coarse_cutoff'] == N//2**h, 'matching probes')
            ref.contains(row['old_response'], dot(a, mean), 'old response')
            ref.contains(row['next_response'], dot(b, mean), 'new response')
            drift = pair(p, a)/2-pair(q, copied)
            ref.contains(row['drift_pairing'], drift, 'signed optimizer drift')
            ref.check(abs(dot(b, mean)-dot(a, mean)/2-drift) < D('1e-85'), 'signed response identity')
            for key, vector in [('old_coefficients', a), ('next_coefficients', b), ('removed_coefficients', correction)]:
                for coefficient in row[key]:
                    ref.contains(coefficient['coefficient'], vector.get(coefficient['clock'], D()), key)
            old.append(a);new.append(b);removed.append(correction)
        ref.check(len(actual['gram']) == len(depths)*(len(depths)+1)//2, 'all Gram cross terms')
        for row in actual['gram']:
            i, j = row['left'], row['right']
            before, after, loss = pair(old[i], old[j]), pair(new[i], new[j]), pair(removed[i], removed[j])
            ref.contains(row['old'], before, 'old complete Gram')
            ref.contains(row['next'], after, 'new complete Gram')
            ref.contains(row['loss'], loss, 'removed complete Gram')
            ref.check(abs(before-loss-after) < D('1e-85'), 'Gram transport identity')
        print(f'PASS fourfold probe transport N={N}, {len(depths)} paired depths', flush=True)
    for args in [('1',), ('9',), ('2x',), ('2', '--json', '--json'), ('2', '--output', 'x')]:
        bad = subprocess.run([binary, 'native-refinement', 'probe-transport', *args], capture_output=True, text=True)
        ref.check(bad.returncode != 0 and not bad.stdout, ('rejected input', args))
    ref.check('probe-transport' in subprocess.check_output([binary, '__complete', 'native-refinement'], text=True), 'completion')
    print(f'PASS native probe transport: {ref.checks} checks; independent complete projections, signed drift, coefficients and all Gram cross terms.')


if __name__ == '__main__':
    main()
