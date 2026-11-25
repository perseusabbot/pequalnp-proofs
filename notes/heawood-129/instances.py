"""Construct the two edge-mask censuses and the projected boundary instances."""
from functools import cache
from hashlib import sha256
from itertools import combinations
from math import comb
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / 'heawood-128'
BASE = HERE.parent / 'heawood-127'
sys.path[:0] = [str(PREVIOUS), str(BASE)]
from boundary import cover_table, cycle_catalog, graph, matching_numbers, orbits, patches
from cycle_census import has_cycle

EDGES = graph(BASE / 'src/HeawoodStages.lean')
ENDS = [(1 << a) | (1 << b) for a, b in EDGES]
ALL = (1 << len(EDGES)) - 1


def endpoints(mask):
    vertices = 0
    for i, pair in enumerate(ENDS):
        if mask >> i & 1:
            vertices |= pair
    return vertices


def census(layers):
    covers, induced = cover_table(EDGES)
    matching = matching_numbers(ENDS)
    if covers != matching:
        raise ValueError('Vertex cover and matching numbers disagree')
    cycles = cycle_catalog(EDGES, induced)
    shapes = patches(EDGES, induced, cycles)
    sixes = [m for claw, _, _, m in shapes if not claw]
    weak = [m for claw, _, _, m in shapes if claw]
    weak.extend(m for vertices, m in cycles.items() if vertices.bit_count() == 8)
    has_six = has_cycle(dict(enumerate(sixes)), ALL)
    has_weak = has_cycle(dict(enumerate(weak)), ALL)
    results = []
    for losses in layers:
        candidates = []
        checked = 0
        for indices in combinations(range(len(EDGES)), losses):
            mask = endpoints_mask = branching = 0
            for i in indices:
                mask |= 1 << i
                branching |= endpoints_mask & ENDS[i]
                endpoints_mask |= ENDS[i]
            checked += 1
            retained = ALL ^ mask
            base = retained.bit_count() + endpoints_mask.bit_count() + matching[retained] - 1
            bonus = 3 if has_six[mask] else 2 if has_weak[mask] else int(bool(induced[branching] & mask))
            if base + bonus <= 26:
                candidates.append(mask)
        if checked != comb(len(EDGES), losses):
            raise ValueError('Incomplete layer')
        group = orbits(EDGES, candidates)
        if group['automorphisms'] != 336 or sum(o['size'] for o in group['orbits']) != len(candidates):
            raise ValueError('Incomplete symmetry cover')
        inventory = b''.join(m.to_bytes(3, 'little') for m in sorted(candidates))
        results.append(dict(losses=losses, checked=checked, candidates=len(candidates),
                            sorted_masks_sha256=sha256(inventory).hexdigest(),
                            automorphisms=group['automorphisms'], orbits=group['orbits']))
    return results


def disjoint_matching(mask):
    retained = [i for i in range(len(EDGES)) if not (mask >> i & 1)]
    for count in range(min(7, len(retained)), -1, -1):
        for chosen in combinations(retained, count):
            if len({v for i in chosen for v in EDGES[i]}) == 2*count:
                return list(chosen)
    raise ValueError('Empty matching missing')


@cache
def maximal_independent(points):
    neighbors = [0]*14
    for a, b in EDGES:
        if points >> a & points >> b & 1:
            neighbors[a] |= 1 << b
            neighbors[b] |= 1 << a
    result = []
    row = points
    while True:
        dominated = row
        for v in range(14):
            if row >> v & 1:
                if row & neighbors[v]:
                    break
                dominated |= neighbors[v]
        else:
            if dominated == points:
                result.append(row)
        if row == 0:
            return sorted(result)
        row = (row-1) & points


def instance(mask, points):
    lost_vertices = endpoints(mask)
    if not points or points & ~lost_vertices:
        raise ValueError('Sampling outside the lost endpoints')
    positive = [e for i, e in enumerate(ENDS) if mask >> i & 1 and e & points == e]
    negative = maximal_independent(points)
    surviving_neighbors = [0]*14
    for i, (a, b) in enumerate(EDGES):
        if not (mask >> i & 1):
            surviving_neighbors[a] |= points & (1 << b)
            surviving_neighbors[b] |= points & (1 << a)
    signals = {1 << v for v in range(14) if points >> v & 1}
    for neighbors in surviving_neighbors:
        subset = neighbors
        while subset:
            signals.add(subset)
            subset = (subset-1) & neighbors
    matching = disjoint_matching(mask)
    budget = 26 - (21-mask.bit_count()) - len(matching) - (lost_vertices & ~points).bit_count()
    return dict(representative=mask, lost_vertices=lost_vertices, sample_vertices=points,
                matching=matching, gate_cap=budget, signals=sorted(signals),
                positive_rows=positive, negative_rows=negative)


def search_line(case, cap=None):
    positive, negative = case['positive_rows'], case['negative_rows']
    words = [sum(1 << i for i, row in enumerate(positive+negative) if row & s) for s in case['signals']]
    header = [case['gate_cap'] if cap is None else cap, len(positive), len(negative), len(words)]
    return ' '.join(map(str, [*header, *words])) + '\n'
