"""Enumerate four missing Heawood edges and independently check their six-vertex covers."""
import argparse
from ast import literal_eval
from collections import Counter, defaultdict
from itertools import combinations
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
STAGES = HERE.parents[1] / '3004/check120/controls/HeawoodStages.lean'


def read_edges(stages):
    line = re.search(r'^def edges.*? := (\[.+\])$', stages.read_text(), re.M)
    edges = literal_eval(line[1])
    if len(edges) != 21 or len(set(edges)) != 21:
        raise ValueError('The source must specify twenty-one distinct edges')
    return edges


def covering_sets(edges, covered, slots):
    """Branch on which endpoint of the first uncovered edge belongs to a cover."""
    if not edges:
        return {tuple(sorted(covered))}
    if not slots:
        return set()
    solutions = set()
    for vertex in edges[0]:
        remaining = [edge for edge in edges if vertex not in edge]
        solutions.update(covering_sets(remaining, (*covered, vertex), slots-1))
    return solutions


def census(stages):
    edges = read_edges(stages)
    positions = set(range(len(edges)))
    incident_counts = Counter()
    witnesses = defaultdict(set)
    for centers in combinations(range(14), 6):
        incident = {i for i, (a, b) in enumerate(edges) if a in centers or b in centers}
        incident_counts[len(incident)] += 1
        if len(incident) < 17:
            continue
        for omitted in combinations(sorted(incident), len(incident)-17):
            lost = tuple(sorted((positions-incident) | set(omitted)))
            witnesses[lost].add(centers)

    degrees = Counter()
    shapes = Counter()
    records = []
    tested_omissions = 0
    for lost in combinations(range(21), 4):
        tested_omissions += 1
        kept = [edge for i, edge in enumerate(edges) if i not in lost]
        independent = covering_sets(kept, (), 6)
        if independent != witnesses.get(lost, set()):
            raise ValueError(f'Independent cover search disagrees on {lost}')
        if not independent:
            continue
        if len(independent) != 1:
            raise ValueError(f'Expected a unique six-center cover for {lost}')
        centers, = independent
        if len(centers) != 6:
            raise ValueError('Seventeen edges need at least six cubic centers')
        multiplicities = Counter(vertex for i in lost for vertex in edges[i])
        shape = ','.join(map(str, sorted(multiplicities.values(), reverse=True)))
        degrees[shape] += 1
        omitted_edges = [edges[i] for i in lost]
        if max(multiplicities.values()) == 3:
            label = 'star with attached edge' if 2 in multiplicities.values() else 'star and disjoint edge'
        else:
            if any(multiplicities[a]==multiplicities[b]==2 for a,b in omitted_edges):
                raise ValueError('The two degree-two vertices are adjacent')
            if sorted(multiplicities.values()) != [1,1,1,1,2,2]:
                raise ValueError('Unexpected four-edge configuration')
            label = 'two disjoint two-edge paths'
        shapes[label] += 1
        records.append(dict(edge_indices=lost, centers=centers))
    return dict(vertex_count=14, edge_count=21, tested_centers=sum(incident_counts.values()),
                tested_omissions=tested_omissions, incident_edge_counts=dict(sorted(incident_counts.items())),
                candidate_count=len(records), omitted_degree_sequences=dict(sorted(degrees.items())),
                omitted_shapes=dict(sorted(shapes.items())), candidates=records)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', type=Path, default=STAGES)
    args = parser.parse_args()
    print(json.dumps(census(args.stages), indent=2))
