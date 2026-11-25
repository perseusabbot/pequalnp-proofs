"""Count all Heawood edge subsets satisfying the endpoint and path inequalities."""
import argparse
from array import array
from ast import literal_eval
from collections import Counter
from itertools import combinations, permutations
import json
from math import comb
from pathlib import Path
import re


def graph(stages):
    match = re.search(r'^def edges.*? := (\[.+\])$', stages.read_text(), re.M)
    edges = literal_eval(match[1])
    if len(set(edges)) != 21 or any(not 0 <= u < 7 <= v < 14 for u, v in edges):
        raise ValueError('Invalid oriented Heawood edge list')
    return edges


def witnesses(edges):
    neighbors = [{b if u == a else a for a, b in edges if u in (a, b)} for u in range(14)]
    rows = []
    for i, (a, b) in enumerate(edges):
        positive = (1 << a) | (1 << b)
        regular = {0} | {1 << v for v in range(14)}
        for v in range(14):
            neighborhood = set(neighbors[v])
            if v in (a, b):
                neighborhood.discard(b if v == a else a)
            for n in range(1, len(neighborhood)+1):
                regular.update(sum(1 << u for u in subset) for subset in combinations(neighborhood, n))
        for target, opposite in ((a, b), (b, a)):
            negative = (1 << opposite) | sum(1 << v for v in range(14)
                if (v < 7) == (target < 7) and v not in neighbors[opposite])
            if any((negative >> u) & (negative >> v) & 1 for u, v in edges):
                raise ValueError('A separating negative contains an edge')
            separators = [s for s in regular if s & positive and not (s & negative)]
            if separators != [1 << target]:
                raise ValueError('The endpoint literal is not forced')
            rows.append(dict(edge=i, target=target, negative=negative))
    return rows


def cover_table(edges):
    count = 1 << len(edges)
    cover = bytearray([15])*count
    induced = array('I', [0])*(1 << 14)
    for vertices in range(1 << 14):
        incident = internal = 0
        for i, (a, b) in enumerate(edges):
            x, y = vertices >> a & 1, vertices >> b & 1
            incident |= (x | y) << i
            internal |= (x & y) << i
        induced[vertices] = internal
        cover[incident] = min(cover[incident], vertices.bit_count())
    # A cover of a superset covers every subset.
    for i in range(len(edges)):
        bit = 1 << i
        for block in range(0, count, 2*bit):
            for mask in range(block, block+bit):
                if cover[mask+bit] < cover[mask]:
                    cover[mask] = cover[mask+bit]
    return cover, induced


def component_degrees(edges, mask):
    neighbors = [set() for _ in range(14)]
    for i, (x, y) in enumerate(edges):
        if mask & (1 << i):
            neighbors[x].add(y)
            neighbors[y].add(x)
    todo = {v for v in range(14) if neighbors[v]}
    pieces = []
    while todo:
        first = todo.pop()
        reached, stack = [first], [first]
        while stack:
            v = stack.pop()
            fresh = neighbors[v] & todo
            todo.difference_update(fresh)
            reached.extend(fresh)
            stack.extend(fresh)
        pieces.append(''.join(str(n) for n in sorted(len(neighbors[v]) for v in reached)))
    return tuple(sorted(pieces))


def orbits(edges, masks):
    # A permutation on one side fixes the images of all seven vertices on
    # the other side, because their three-neighbor sets are pairwise distinct.
    hood = [{y if x == v else x for x,y in edges if v in (x,y)} for v in range(14)]
    lookup = {frozenset(row):v for v,row in enumerate(hood)}
    edge_index = {frozenset(edge):i for i,edge in enumerate(edges)}
    mappings = []
    for first_side in (range(7), range(7,14)):
        for images in permutations(first_side):
            right = [lookup.get(frozenset(images[x] for x in hood[v])) for v in range(7,14)]
            if None in right:
                continue
            perm = [*images,*right]
            if len(set(perm)) != 14:
                raise ValueError('The vertex map is not a permutation')
            action = [edge_index[frozenset((perm[x],perm[y]))] for x,y in edges]
            if len(set(action)) != 21:
                raise ValueError('The map does not preserve the edge set')
            mappings.append(action)
    if len(set(map(tuple,mappings))) != len(mappings):
        raise ValueError('Duplicate action on edges')
    remaining = set(masks)
    classes = []
    while remaining:
        root = min(remaining)
        ids = [i for i in range(21) if root & (1 << i)]
        orbit = {sum(1 << p[i] for i in ids) for p in mappings}
        if not orbit <= remaining:
            raise ValueError('The candidates are not a union of disjoint orbits')
        classes.append(dict(representative=root, edge_indices=ids, edges=[edges[i] for i in ids],
                            size=len(orbit), stabilizer=len(mappings)//len(orbit)))
        remaining.difference_update(orbit)
    return dict(automorphisms=len(mappings),orbits=classes)


def census(edges):
    cover, induced = cover_table(edges)
    total = 1 << len(edges)
    pair = [(1 << u) | (1 << v) for u, v in edges]
    endpoints = array('H', [0])*total
    branching = array('H', [0])*total
    counts = [Counter() for _ in range(22)]
    best = [None]*22
    six_before_path = Counter()
    eight_boundary = []
    induced_eight = 0
    eight_shapes = Counter()
    for mask in range(total):
        if mask:
            bit = mask & -mask
            rest, ends = mask ^ bit, pair[bit.bit_length()-1]
            endpoints[mask] = endpoints[rest] | ends
            branching[mask] = branching[rest] | (endpoints[rest] & ends)
        m = mask.bit_count()
        vertices = endpoints[mask].bit_count()
        centers = cover[(total-1) ^ mask]
        # In this triangle-free graph an edge between two branching vertices
        # extends to a simple three-edge path. Girth six ensures it is induced.
        path = bool(induced[branching[mask]] & mask)
        rank_bound = 21 - m + centers + vertices - 1
        floor = rank_bound + int(path)
        counts[m][floor] += 1
        if best[m] is None or floor < best[m]['floor']:
            best[m] = dict(floor=floor, mask=mask, vertices=vertices, cover=centers, path=path)
        if m == 8 and floor <= 26:
            eight_boundary.append(mask)
            induced_eight += int(induced[endpoints[mask]] == mask)
            eight_shapes[component_degrees(edges, mask)] += 1
        if m == 6 and rank_bound <= 26:
            six_before_path[(centers, vertices, path)] += 1
    if any(sum(row.values()) != comb(21, i) for i, row in enumerate(counts)):
        raise ValueError('Incomplete edge subset inventory')
    return dict(edge_subsets=total, minimum_by_losses=best,
                eight_edge_masks=eight_boundary, eight_induced=induced_eight,
                eight_symmetries=orbits(edges, eight_boundary),
                eight_component_degrees=[dict(components=k, count=n) for k,n in sorted(eight_shapes.items())],
                floor_histograms=[dict(sorted(row.items())) for row in counts],
                six_before_path=[dict(cover=c, vertices=v, path=p, count=n)
                    for (c,v,p),n in sorted(six_before_path.items())])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', required=True, type=Path)
    args = parser.parse_args()
    edges = graph(args.stages)
    print(json.dumps(dict(singleton_witnesses=witnesses(edges), **census(edges)), indent=2))


if __name__ == '__main__':
    main()
