"""Replay the two new exact searches per test, every prefix certificate and the complete frontier."""
import argparse
import gzip
import json
from pathlib import Path
import sys
import tempfile

from transport import DIRECT, HERE, PARENT, disjoint_matching, endpoints, instance, inventory, read
from prefix import PrefixProblem, check, gate
from controls import circuits
sys.path.insert(0, str(PARENT))
from verify import compile_engines, controls, run_both


def new_searches(directory):
    binaries = compile_engines(directory)
    small = controls(binaries)
    direct = []
    for m, t in DIRECT:
        case = instance(m, t)
        record = run_both(binaries, case, case['gate_cap'])
        check(not record['possible'], 'A projected test admits a short circuit')
        direct.append(dict(mask=m, vertices=t, cap=case['gate_cap'], **record))
    return small, direct


def rejection_controls(cert):
    problem = PrefixProblem(cert['mask'], cert['vertices'], cert['cap'])
    tested = []
    def reject(message, test):
        try:
            test()
        except ValueError as err:
            if str(err) != message:
                raise
        else:
            raise ValueError('Malformed proof accepted')
        tested.append(message)
    # This full-graph branch deletes four vertices and the second prefix result.
    ops = [(1, 1, 0), (1, 2, 0)]
    tree, wires = cert['tree'], list(problem.base)
    for op in ops:
        kind, a, b = op
        tree = next(row[3] for row in tree if tuple(row[:3]) == op)
        wires.append(gate(kind, wires[a], wires[b]))
    source, symmetry, ports, lifts = cert['witnesses'][tree]
    reject('A possible minimum-circuit gate is missing',
           lambda: problem.audit(dict(cert, tree=cert['tree'][1:])))
    reject('Incorrect negative row lift', lambda: problem.leaf(
        [source, symmetry, ports, [0, *lifts[1:]]], wires, ops))
    reject('A positive implication fails', lambda: problem.leaf(
        [source, symmetry, [0, *ports[1:]], lifts], wires, ops))
    larger = PrefixProblem(problem.mask, problem.vertices, 23)
    reject('Gate count fails at this leaf', lambda: larger.leaf(
        [source, symmetry, ports, lifts], wires, ops))
    return tested


def certified_bounds():
    tests = json.loads(gzip.decompress((HERE/'prefixes.json.gz').read_bytes()))
    prior_sources = read(PARENT/'screens.json')
    previous = read(PARENT/'results.json')
    records = {a['representative']: a for l in previous['layers'] for a in l['exhaustions']}
    records.update({a['representative']: a for a in previous['additional_checks']})
    check(set(records) == {c['representative'] for c in prior_sources}
          and all(not a['possible'] for a in records.values()), 'Unaccounted source decision')
    summaries, bounds = [], {}
    global_floor = 0
    full_test = None
    for cert in tests:
        m, v, cap = (cert[key] for key in ('mask', 'vertices', 'cap'))
        proof = PrefixProblem(m, v, cap)
        stats = proof.audit(cert)
        # For an all-edges mask every primary input is a vertex singleton.
        if m == (1 << 21)-1 and v == (1 << 14)-1:
            check(proof.inputs == [1 << i for i in range(14)], 'Wrong full graph alphabet')
            check(len(proof.positive) == 21 and len(proof.negative) == 37, 'Wrong full graph rows')
            global_floor = max(global_floor, cap+1)
            full_test = cert
        bound = cap+1 + (21-m.bit_count()) + len(disjoint_matching(m)) + (endpoints(m) & ~v).bit_count()
        bounds[m] = max(bounds.get(m, 0), bound)
        summaries.append(dict(**stats, original_gate_floor=bound))
    check(global_floor > 0, 'Missing full graph certificate')
    return summaries, inventory(global_floor, bounds.items()), rejection_controls(full_test)


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('--write', action='store_true', help='write the reconstructed results')
    args = args.parse_args()
    with tempfile.TemporaryDirectory() as directory:
        small, direct = new_searches(Path(directory))
    prefixes, frontier, rejected = certified_bounds()
    # JSON objects always use string keys. Normalize integer-keyed histograms.
    report = json.loads(json.dumps(dict(controls=small, direct=direct, prefixes=prefixes, rejected_controls=rejected)))
    for name, data in [('results.json', report), ('frontier.json', frontier), ('controls.json', circuits())]:
        if args.write:
            (HERE/name).write_text(json.dumps(data, indent=1)+'\n')
        else:
            check(read(HERE/name) == data, 'Published data differs in '+name)
    print(f"Verified {len(direct)} exact tests and {len(prefixes)} prefix certificates. "
          f"Full graph lower bound {frontier['global_gate_floor']}. "
          f"{frontier['remaining_masks']} labeled sets in {frontier['remaining_orbits']} classes remain.")


if __name__ == '__main__':
    main()
