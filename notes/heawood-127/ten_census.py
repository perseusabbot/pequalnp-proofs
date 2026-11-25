"""Reproduce the 22 gate floors, the ten-loss orbit, and its Lean witnesses."""
import argparse
from array import array
from collections import Counter
from itertools import combinations, permutations, product
import json
from math import comb
from pathlib import Path

from census import component_degrees, cover_table, graph
from cycle_census import cycle_catalog, has_cycle


def neighborhoods(edges):
    return [sorted(y if x == v else x for x, y in edges if v in (x, y)) for v in range(14)]


def patches(edges, induced, cycles):
    near = neighborhoods(edges)
    result = []
    for d, mask in cycles.items():
        if d.bit_count() != 6:
            continue
        within = {v: [u for u in near[v] if d & (1 << u)] for v in range(14) if d & (1 << v)}
        start = min(within)
        order = [start, min(within[start])]
        while len(order) < 6:
            order.append(next(v for v in within[order[-1]] if v != order[-2]))
        result.append((False, order, d, mask))
    for center in range(14):
        middle = near[center]
        for tips in product(*[[v for v in near[y] if v != center] for y in middle]):
            order = [center, *middle, *tips]
            d = sum(1 << v for v in order)
            mask = induced[d]
            if len(set(order)) != 7 or mask.bit_count() != 6:
                raise ValueError('The seven vertices do not induce a subdivided claw')
            result.append((True, order, d, mask))
    if len({d for _, _, d, _ in result}) != len(result):
        raise ValueError('Repeated vertex set in the restriction inventory')
    return sorted(result, key=lambda r: (r[0], r[2]))


def enumerate_automorphisms(edges):
    near = neighborhoods(edges)
    by_neighbors = {frozenset(row): v for v, row in enumerate(near)}
    index = {frozenset(e): i for i, e in enumerate(edges)}
    for side in (range(7), range(7, 14)):
        for left in permutations(side):
            right = [by_neighbors.get(frozenset(left[u] for u in near[v])) for v in range(7, 14)]
            if None in right:
                continue
            mapping = [*left, *right]
            action = [index[frozenset((mapping[u], mapping[v]))] for u, v in edges]
            if len(set(mapping)) != 14 or len(set(action)) != 21:
                raise ValueError('Invalid automorphism')
            yield mapping, action


def orbit(edges, candidates):
    representative = min(candidates)
    indices = [i for i in range(21) if representative & (1 << i)]
    seen, actions = {}, set()
    for mapping, action in enumerate_automorphisms(edges):
        action = tuple(action)
        if action in actions:
            raise ValueError('Repeated edge action')
        actions.add(action)
        mask = sum(1 << action[i] for i in indices)
        seen.setdefault(mask, mapping)
    if set(seen) != set(candidates):
        raise ValueError('The ten-loss candidates are not one full orbit')
    orbit_info = dict(representative=representative, edge_indices=indices, edges=[edges[i] for i in indices],
                      automorphisms=len(actions), size=len(seen), stabilizer=len(actions)//len(seen))
    return orbit_info, sorted(seen.items())


def restriction(edges, mask):
    missing = [e for i, e in enumerate(edges) if mask & (1 << i)]
    retained = [e for i, e in enumerate(edges) if not mask & (1 << i)]
    vertices = sorted({v for e in missing for v in e})
    active = set(vertices)
    if [e for e in edges if set(e) <= active] != missing:
        raise ValueError('The missing graph is not induced on its endpoints')
    available = set()
    for center in range(14):
        local = sorted((y if x == center else x) for x, y in retained if center in (x,y)
                       and (y if x == center else x) in active)
        for n in range(2, len(local)+1):
            available.update(combinations(local, n))
    groups = sorted(available)
    # Initial ports are the endpoint singletons followed by the optional ORs.
    # This control deliberately uses only singleton ports.
    gates, products = [], []
    inputs = len(vertices)+len(groups)
    def append(op, a, b):
        gates.append([op, a, b])
        return inputs+len(gates)-1
    for center in sorted({u for u, _ in missing}):
        neighbors = [vertices.index(v) for u, v in missing if u == center]
        joined = neighbors[0]
        for other in neighbors[1:]:
            joined = append('OR', joined, other)
        products.append(append('AND', vertices.index(center), joined))
    output = products[0]
    for term in products[1:]:
        output = append('OR', output, term)
    for row in range(1 << len(vertices)):
        values = [bool(row & (1 << i)) for i in range(len(vertices))]
        values.extend(any(values[vertices.index(v)] for v in group) for group in groups)
        for op, a, b in gates:
            values.append((values[a] or values[b]) if op == 'OR' else (values[a] and values[b]))
        expected = any(values[vertices.index(u)] and values[vertices.index(v)] for u, v in missing)
        if values[output] != expected:
            raise ValueError('Restricted positive control failed')
    return dict(vertex_order=vertices, allowed_extra_disjunctions=groups, missing_edges=missing,
                induced_assignments=1 << len(vertices), necessary_gate_limit=11,
                control_gates=gates, control_output_port=output)


def census(edges, cover, induced, cycles, patterns):
    full = (1 << 21)-1
    six = {d: m for claw, _, d, m in patterns if not claw}
    claws = {d: m for claw, _, d, m in patterns if claw}
    eights = {d: m for d, m in cycles.items() if d.bit_count() == 8}
    has_six, has_claw, has_eight = [has_cycle(table, full) for table in (six, claws, eights)]
    ends = [(1 << u) | (1 << v) for u, v in edges]
    vertices = array('H', [0]) * (full+1)
    branching = array('H', [0]) * (full+1)
    histograms = [Counter() for _ in range(22)]
    old_nine, ten = [], []
    old_core_types, ten_profiles = Counter(), Counter()
    for mask in range(full+1):
        if mask:
            bit = mask & -mask
            other, pair = mask ^ bit, ends[bit.bit_length()-1]
            vertices[mask] = vertices[other] | pair
            branching[mask] = branching[other] | (vertices[other] & pair)
        m = mask.bit_count()
        v = vertices[mask].bit_count()
        j = cover[full ^ mask]
        path = bool(induced[branching[mask]] & mask)
        six_cycle, claw, eight_cycle = bool(has_six[mask]), bool(has_claw[mask]), bool(has_eight[mask])
        if (six_cycle or claw or eight_cycle) and not path:
            raise ValueError('Missing path inside a larger restriction')
        base = 21-m+v+j-1
        previous = base + (2 if six_cycle or eight_cycle else int(path))
        extra = 3 if six_cycle else 2 if claw or eight_cycle else int(path)
        floor = base+extra
        histograms[m][floor] += 1
        if m == 9 and previous <= 26:
            if floor <= 26:
                raise ValueError('A previous nine-loss case passed the new bound')
            old_nine.append(mask)
            old_core_types[(six_cycle, claw)] += 1
        if m == 10 and floor <= 26:
            ten.append(mask)
            ten_profiles[(v, j, induced[vertices[mask]] == mask, sum(q & mask == q for q in six.values()),
                          sum(q & mask == q for q in eights.values()), component_degrees(edges, mask))] += 1
    if any(sum(row.values()) != comb(21, m) for m, row in enumerate(histograms)):
        raise ValueError('Incomplete edge subset census')
    symmetry, relabelings = orbit(edges, ten)
    return dict(edge_subsets=full+1, restrictions=dict(six_cycles=len(six), subdivided_claws=len(claws),
                eight_cycles=len(eights)), minimum_by_losses=[min(row) for row in histograms],
                floor_histograms=[dict(sorted(row.items())) for row in histograms], previous_nine_masks=old_nine,
                nine_cases=[dict(six_cycle=s, subdivided_claw=c, count=n) for (s, c), n in sorted(old_core_types.items())],
                ten_edge_masks=ten, ten_orbit=symmetry,
                representative_restriction=restriction(edges, symmetry['representative']),
                ten_profiles=[dict(endpoints=v, minimum_cover=j, induced=ind, six_cycles=n6,
                                   eight_cycles=n8, component_degrees=seq, count=n)
                              for (v,j,ind,n6,n8,seq),n in sorted(ten_profiles.items())]), relabelings


def lean_list(items):
    return '[' + ','.join(map(str, items)) + ']'


def render_patches(patterns):
    lines = ['import Mathlib.Data.Nat.Basic', '', 'namespace Checkpoint127.Heawood', '',
             'structure Patch where', '  claw : Bool', '  order : List (Fin 14)', '  d : ℕ', '  mask : ℕ',
             '', 'def patches : List Patch := [']
    for claw, vs, d, m in patterns:
        lines.append(f'  ⟨{str(claw).lower()},{lean_list(vs)},{d},{m}⟩,')
    lines[-1] = lines[-1][:-1]
    return '\n'.join([*lines, ']', '', 'end Checkpoint127.Heawood', ''])


def render_masks(masks):
    chunks = [','.join(map(str, masks[i:i+12])) for i in range(0, len(masks), 12)]
    return ('import Mathlib.Data.Nat.Basic\n\nnamespace Checkpoint127.Ten\n\n'
            '/-- The single ten-loss candidate orbit, in ascending edge-mask order. -/\n'
            'def masks : List ℕ := [\n  ' + ',\n  '.join(chunks) + '\n]\n\nend Checkpoint127.Ten\n')


def render_relabelings(rows):
    return ('import Mathlib.Data.Nat.Basic\n\nnamespace Checkpoint127.Ten\n\n'
            '/-- An explicit Heawood relabeling for each candidate mask. -/\n'
            'def relabelings : List (ℕ × List (Fin 14)) := [\n' +
            ',\n'.join(f'  ({m},{lean_list(p)})' for m, p in rows) + '\n]\n\nend Checkpoint127.Ten\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', type=Path, default=Path(__file__).resolve().parent/'src'/'HeawoodStages.lean')
    parser.add_argument('--lean', choices=['patches', 'masks', 'relabelings'])
    args = parser.parse_args()
    edges = graph(args.stages)
    cover, induced = cover_table(edges)
    cycles = cycle_catalog(edges, induced)
    restrictions = patches(edges, induced, cycles)
    if args.lean == 'patches':
        print(render_patches(restrictions), end='')
        return
    report, relabelings = census(edges, cover, induced, cycles, restrictions)
    if args.lean == 'masks':
        print(render_masks(report['ten_edge_masks']), end='')
    elif args.lean == 'relabelings':
        print(render_relabelings(relabelings), end='')
    else:
        print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
