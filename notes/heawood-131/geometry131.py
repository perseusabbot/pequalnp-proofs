"""Reconstruct each signed row test from the graph and its earlier numerical floor."""
from functools import cache
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / 'heawood-130'
sys.path.insert(0, str(PREVIOUS))
from transport import (EDGE_INDEX, disjoint_matching, endpoints, extra_code, fano_actions,
                       full_graph_control, instance, moved, read, restricted_extras, source_screens)

ALL = (1 << 21) - 1
GROUP = fano_actions()[0]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parent_floors():
    rows = [(r['representative'], r['sample_vertices'], r['gate_cap'] + 1) for r in source_screens()]
    rows.extend((r['mask'], r['vertices'], r['cap'] + 1) for r in read(PREVIOUS/'results.json')['prefixes'])
    floors = {}
    for mask, vertices, lower in rows:
        key = mask, vertices
        floors[key] = max(floors.get(key,0),lower)
    return floors


@cache
def sample(mask, vertices):
    return instance(mask, vertices)


def column(word, rows):
    return sum(1 << i for i, row in enumerate(rows) if word & row)


def encode(job, known):
    mask, vertices, cap = job['mask'], job['vertices'], job['cap']
    root = sample(mask, vertices)
    pos, neg = root['positive_rows'], root['negative_rows']
    columns = [column(s, pos + neg) for s in root['signals']]
    lines = [[cap, len(pos), len(neg), len(columns), len(job['tests'])], columns]
    group_vertices = {tuple(perm) for _, perm in GROUP}
    for spec in job['tests']:
        m, t, lower = spec['source']
        require(known.get((m, t), -1) >= lower, 'Unsupported local lower bound')
        perm = tuple(spec['permutation'])
        require(perm in group_vertices, 'Relabeling is outside the graph symmetry group')
        local = sample(m, t)
        domain = moved(t, perm)
        require(domain & ~vertices == 0, 'Local domain leaves the root')
        def mapped(key):
            return sorted(moved(w, perm) for w in local[key])
        p, n, palette = (mapped(k) for k in ('positive_rows','negative_rows','signals'))
        require(set(p) <= set(pos), 'Missing positive edge')
        lifts = spec['negative_lifts']
        require(len(lifts) == len(n) and len(set(lifts)) == len(n), 'Missing or duplicate negative lift')
        require(all(r in neg and r & domain == s for r, s in zip(lifts,n)), 'Incorrect negative lift')
        require(all((s & domain) in [0, *palette] for s in root['signals']), 'Missing projected input')
        p_bits = sum(1 << pos.index(r) for r in p)
        n_bits = sum(1 << (len(pos) + neg.index(r)) for r in lifts)
        # Signals use local negative evaluations on the shared lifts. An outside
        # vertex of a lift may make a root column larger than its replacement.
        free = sorted({(column(s,pos) & p_bits) |
                       sum(1 << (len(pos) + neg.index(r)) for r, a in zip(lifts,n) if s & a)
                       for s in palette})
        lines.extend([[lower, p_bits, n_bits, len(free)], free])
    return ''.join(' '.join(map(str, row)) + '\n' for row in lines)


def serial_cases():
    return read(HERE/'projections.json')
