"""Classify the census by all vertex relabellings preserving the Heawood edges."""
import argparse
from collections import deque
from itertools import permutations
import json
from pathlib import Path
import re

from census import read_edges, STAGES

HERE = Path(__file__).resolve().parent
DUALITY = tuple((v + 7) % 14 for v in range(14))
COLLINEATION = (0, 2, 3, 6, 5, 4, 1, 8, 7, 13, 10, 9, 11, 12)
IDENTITY = tuple(range(14))


def all_relabellings(edges):
    neighbors = [{b if a == v else a for a, b in edges if v in (a, b)} for v in range(14)]
    reached = {0}
    queue = deque([0])
    while queue:
        v = queue.popleft()
        queue.extend(neighbors[v] - reached)
        reached.update(neighbors[v])
    if len(reached) != 14 or not all(a < 7 <= b for a, b in edges):
        raise ValueError('Expected a connected graph with the indicated bipartition')
    blocks = [frozenset(neighbors[v]) for v in range(7, 14)]
    block_index = {block: i + 7 for i, block in enumerate(blocks)}
    if len(block_index) != 7:
        raise ValueError('The seven right-hand neighborhoods must be distinct')
    result = set()
    # On a connected bipartite graph each automorphism either preserves both
    # parts or exchanges them. For the former, the left permutation forces
    # every right image. The fixed duality accounts for the latter.
    for left in permutations(range(7)):
        images = [frozenset(left[x] for x in block) for block in blocks]
        if all(block in block_index for block in images):
            mapping = left + tuple(block_index[block] for block in images)
            result.add(mapping)
            result.add(tuple(DUALITY[x] for x in mapping))
    for mapping in result:
        if set(mapping) != set(IDENTITY) or {tuple(sorted((mapping[a], mapping[b]))) for a, b in edges} != set(edges):
            raise ValueError('A candidate relabelling changes the edge list')
    return result


def word_table():
    # Start at binary 1. Append 0 for the duality or 1 for the collineation.
    words = {IDENTITY: 1}
    queue = deque([IDENTITY])
    while queue:
        mapping = queue.popleft()
        for bit, generator in enumerate((DUALITY, COLLINEATION)):
            image = tuple(generator[x] for x in mapping)
            if image not in words:
                words[image] = 2 * words[mapping] + bit
                queue.append(image)
    return words


def fixed_openings(statement, edges, group, candidates):
    posted = statement.read_text()
    keys = [int(x) for x in re.findall(r'\((\d+) : ℕ\)', posted[posted.index('([['):posted.index(']].getD')])]
    if len(keys) != 65:
        raise ValueError('Expected 65 opening keys')
    index = {edge: i for i, edge in enumerate(edges)}
    actions = {p: [index[tuple(sorted((p[a], p[b])))] for a, b in edges] for p in group}
    results = []
    for i, key in enumerate(keys):
        first, second = (0, key // 225 % 14), (key % 225 // 15, key % 15)
        stabilizer = []
        for p, action in actions.items():
            ports = p + (14,)  # keep the first gate's output wire fixed
            if all(sorted(ports[v] for v in pair) == sorted(pair) for pair in (first, second)):
                stabilizer.append(action)
        remaining = set(candidates)
        orbit_count = 0
        while remaining:
            rep = min(remaining)
            orbit = {tuple(sorted(s[j] for j in rep)) for s in stabilizer}
            if not orbit <= remaining:
                raise ValueError('Inconsistent orbit partition for a fixed opening')
            remaining -= orbit
            orbit_count += 1
        fixed = sum(sum(tuple(sorted(s[j] for j in m)) == m for m in candidates) for s in stabilizer)
        if fixed != len(stabilizer) * orbit_count:
            raise ValueError('Fixed-point and direct orbit counts disagree')
        results.append(dict(index=i, gates=[first, second], automorphisms=len(stabilizer), orbits=orbit_count))
    return results


def classify(stages, census, statement):
    edges = read_edges(stages)
    edge_index = {edge: i for i, edge in enumerate(edges)}
    group = all_relabellings(edges)
    words = word_table()
    if group != words.keys():
        raise ValueError('The two generators do not give the full automorphism group')
    remaining = {tuple(row['edge_indices']) for row in json.loads(census.read_bytes())['candidates']}
    openings = fixed_openings(statement, edges, group, remaining)
    classes = []
    witnesses = []
    while remaining:
        representative = min(remaining)
        mask = sum(1 << i for i in representative)
        orbit = {}
        for mapping, word in words.items():
            image = []
            for index in representative:
                a, b = edges[index]
                image.append(edge_index[tuple(sorted((mapping[a], mapping[b])))])
            image = tuple(sorted(image))
            orbit[image] = min(orbit.get(image, word), word)
        if not orbit.keys() <= remaining:
            raise ValueError('An image is outside the census or meets an earlier orbit')
        classes.append(dict(edge_indices=representative, mask=mask, size=len(orbit),
                            stabilizer=len(group) // len(orbit)))
        for image, word in sorted(orbit.items()):
            witnesses.append([sum(1 << i for i in image), mask, word])
        remaining -= orbit.keys()
    return dict(automorphisms=len(group), generators=[DUALITY, COLLINEATION],
                orbits=classes, witnesses=sorted(witnesses), fixed_openings=openings)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', type=Path, default=STAGES)
    parser.add_argument('--census', type=Path, default=HERE / 'census.json')
    parser.add_argument('--statement', type=Path, default=HERE.parents[1] / 'check122/heawood/statement.txt')
    args = parser.parse_args()
    print(json.dumps(classify(args.stages, args.census, args.statement), indent=2))
