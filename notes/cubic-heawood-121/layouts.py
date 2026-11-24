"""Enumerate the distinct bottom-stage supports of the 27-gate Heawood star circuits."""
import argparse
import ast
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
EDGES = HERE.parents[1] / '3004/check120/controls/HeawoodStages.lean'


def classify(stage_source=EDGES):
    edges = ast.literal_eval(re.search(r'^def edges.*?:= (\[.+\])$', stage_source.read_text(), re.M)[1])
    neighbors = [set() for _ in range(14)]
    raw = [sum(1 << x for x in range(1 << 14) if x & (1 << v)) for v in range(14)]
    target = 0
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
        target |= raw[u] & raw[v]
    libraries = set()
    counts = []
    for centers in (range(7), range(7, 14)):
        choices = [list(combinations(sorted(neighbors[c]), 2)) for c in centers]
        start = len(libraries)
        for pairs in product(*choices):
            signals = raw.copy()
            supports = []
            for c, (u, v) in zip(centers, pairs):
                w, = neighbors[c] - {u, v}
                signals.append(signals[u] | signals[v])
                signals.append(signals[-1] | signals[w])
                supports.extend(((1 << u) | (1 << v), (1 << u) | (1 << v) | (1 << w)))
            for i, c in enumerate(centers):
                signals.append(signals[c] & signals[15+2*i])
            for wire in range(29, 35):
                acc = 28 if wire == 29 else len(signals)-1
                signals.append(signals[acc] | signals[wire])
            if len(signals)-len(raw) != 27 or signals[-1] != target:
                raise ValueError('Invalid 27-gate construction')
            signature = tuple(sorted(supports))
            if signature in libraries or len(set(signature)) != 14:
                raise ValueError('Duplicate bottom-stage support family')
            libraries.add(signature)
        counts.append(len(libraries)-start)
    fingerprint = sha256(b''.join(v.to_bytes(2,'big') for row in sorted(libraries) for v in row)).hexdigest()
    return dict(point_centered=counts[0], line_centered=counts[1], total=len(libraries),
                assignments_checked_per_circuit=1 << 14, gates_per_circuit=27,
                sorted_library_signatures_sha256=fingerprint)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', type=Path, default=EDGES, help='path to HeawoodStages.lean')
    print(json.dumps(classify(parser.parse_args().stages), indent=2))
