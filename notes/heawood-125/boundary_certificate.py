"""Encode the intermediate results of Lean's five-center enumeration in small blocks."""
import argparse
from itertools import combinations
from pathlib import Path

from census import graph


def render(stages):
    edges = graph(stages)
    # Lean's sublistsLen visits the branch without the head of the list first.
    center_sets = list(reversed(list(combinations(range(14), 5))))
    blocks = []
    for k in range(0, len(center_sets), 32):
        masks = []
        for cs in center_sets[k:k+32]:
            covered = [i for i, (x, y) in enumerate(edges) if x in cs or y in cs]
            outside = [i for i in range(21) if i not in covered]
            if len(outside) > 8:
                continue
            for extra in reversed(list(combinations(covered, 8-len(outside)))):
                omitted = outside + list(extra)
                if len({v for i in omitted for v in edges[i]}) == 8:
                    masks.append(sum(1 << i for i in omitted))
        blocks.append(masks)
    unique = sorted(set(x for row in blocks for x in row))
    origins = [next(b for b, items in enumerate(blocks) if mask in items) for mask in unique]
    def rows(values):
        return '[\n  ' + ',\n  '.join(map(str, values)) + '\n]'
    return ('import Mathlib.Data.Nat.Basic\n\nnamespace Checkpoint125.BoundaryData\n\n'
            '-- The kernel compares each of these lists with the five-center enumeration.\n'
            'def blocks : List (List ℕ) := ' + rows(blocks) + '\n\n'
            'def sortedMasks : List ℕ := ' + rows(unique) + '\n\n'
            'def origins : List ℕ := ' + str(origins) + '\n\nend Checkpoint125.BoundaryData\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stages', required=True, type=Path)
    print(render(p.parse_args().stages), end='')
