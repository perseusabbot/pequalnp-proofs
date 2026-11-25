"""Enumerate induced cycles, gate floors, and the nine-loss boundary."""
import argparse
from array import array
from collections import Counter
from itertools import combinations
import json
from math import comb
from pathlib import Path

from census import component_degrees, cover_table, graph, orbits


def cycle_catalog(edges, induced):
    cores = {}
    for n in (6, 8):
        for vertices in combinations(range(14), n):
            vertex_mask = sum(1 << v for v in vertices)
            edge_mask = induced[vertex_mask]
            if edge_mask.bit_count() == n and component_degrees(edges, edge_mask) == ('2' * n,):
                cores[vertex_mask] = edge_mask
    return dict(sorted(cores.items()))


def has_cycle(cores, full_mask):
    present = bytearray(full_mask + 1)
    for cycle in cores.values():
        complement = full_mask ^ cycle
        extra = complement
        while True:
            present[cycle | extra] = 1
            if not extra:
                break
            extra = (extra - 1) & complement
    return present


def cycle_data(cores):
    rows = ',\n'.join(f'  ({d},{m})' for d, m in cores.items())
    return ('import Mathlib.Data.Nat.Basic\n\nnamespace Checkpoint126.Heawood\n\n'
            '/-- Vertex and edge masks for the induced six- and eight-cycles. -/\n'
            'def cores : List (ℕ × ℕ) := [\n' + rows + '\n]\n\nend Checkpoint126.Heawood\n')


def nine_data(edges, induced, masks):
    # Each exceptional eight-vertex set has a six-edge matching in its complement.
    proofs = set()
    for d, internal in enumerate(induced):
        if d.bit_count() != 8 or internal.bit_count() < 9:
            continue
        outside = [i for i in range(21) if not (internal >> i) & 1]
        for candidate in combinations(outside, 6):
            if len({v for i in candidate for v in edges[i]}) == 12:
                proofs.add(candidate)
                break
        else:
            raise ValueError(f'No six-edge matching for vertex set {d}')
    proof_rows = ',\n  '.join('[' + ','.join(map(str, es)) + ']' for es in sorted(proofs))
    mask_rows = ',\n  '.join(','.join(map(str, masks[i:i+12])) for i in range(0, len(masks), 12))
    return ('import Mathlib.Data.Nat.Basic\n\nnamespace Checkpoint126.Nine\n\n'
            '/-- Six disjoint surviving edges for small endpoint sets. -/\n'
            'def matchings : List (List (Fin 21)) := [\n  ' + proof_rows + '\n]\n\n'
            '/-- The nine-edge candidate masks in ascending order. -/\n'
            'def masks : List ℕ := [\n  ' + mask_rows + '\n]\n\nend Checkpoint126.Nine\n')


def census(edges, cover, induced, cores):
    total = 1 << len(edges)
    full = total - 1
    present = has_cycle(cores, full)
    pairs = [(1 << u) | (1 << v) for u, v in edges]
    endpoints = array('H', [0]) * total
    branching = array('H', [0]) * total
    histograms = [Counter() for _ in range(22)]
    old_eight = []
    boundary = []
    profiles = Counter()
    for mask in range(total):
        if mask:
            bit = mask & -mask
            rest = mask ^ bit
            ends = pairs[bit.bit_length()-1]
            endpoints[mask] = endpoints[rest] | ends
            branching[mask] = branching[rest] | (endpoints[rest] & ends)
        m = mask.bit_count()
        v = endpoints[mask].bit_count()
        j = cover[full ^ mask]
        # Both endpoints of an internal path edge have missing degree at least two.
        path = bool(induced[branching[mask]] & mask)
        cycle = bool(present[mask])
        if cycle and not path:
            raise ValueError(f'Cycle without a three-edge path at mask {mask}')
        previous = 21 - m + v + j - 1 + int(path)
        floor = previous + int(cycle)
        histograms[m][floor] += 1
        if m == 8 and previous <= 26:
            old_eight.append(mask)
        if m == 9 and floor <= 26:
            boundary.append(mask)
            profiles[(v, j, path, cycle, induced[endpoints[mask]] == mask)] += 1
    if any(sum(row.values()) != comb(21, m) for m, row in enumerate(histograms)):
        raise ValueError('Incomplete edge subset census')
    if any(not present[mask] for mask in old_eight):
        raise ValueError('An eight-loss candidate in the previous checkpoint is missing a cycle')
    classes = orbits(edges, boundary)
    for row in classes['orbits']:
        mask = row['representative']
        row['degree_sequences_by_component'] = component_degrees(edges, mask)
        row['contained_cycle_sizes'] = sorted(q.bit_count() for q in cores.values() if q & mask == q)
        row['endpoint_vertices'] = [v for v in range(14) if (endpoints[mask] >> v) & 1]
        row['induced_edges'] = induced[endpoints[mask]].bit_count()
    return dict(edge_subsets=total, cycle_counts=dict(sorted(Counter(c.bit_count() for c in cores.values()).items())),
                minimum_by_losses=[min(row) for row in histograms],
                floor_histograms=[dict(sorted(row.items())) for row in histograms],
                old_eight_count=len(old_eight), old_eight_with_cycle=sum(present[m] for m in old_eight),
                old_eight_masks=old_eight, nine_edge_masks=boundary,
                nine_profiles=[dict(vertices=v, minimum_cover=j, path=p, cycle=c, induced=i, count=n)
                               for (v, j, p, c, i), n in sorted(profiles.items())], nine_symmetries=classes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', type=Path, default=Path(__file__).resolve().parent/'src'/'HeawoodStages.lean')
    output = parser.add_mutually_exclusive_group()
    output.add_argument('--lean-nine', action='store_true', help='emit the matching witnesses and candidate masks')
    output.add_argument('--lean-cycles', action='store_true', help='emit the Lean table of vertex and edge masks')
    args = parser.parse_args()
    edges = graph(args.stages)
    cover, induced = cover_table(edges)
    cores = cycle_catalog(edges, induced)
    if args.lean_cycles:
        print(cycle_data(cores), end='')
    else:
        result = census(edges, cover, induced, cores)
        if args.lean_nine:
            print(nine_data(edges, induced, result['nine_edge_masks']), end='')
        else:
            print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
