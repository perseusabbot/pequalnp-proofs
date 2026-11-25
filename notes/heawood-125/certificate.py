"""Build the matching witnesses for Lean's independent 14-vertex certificate."""
import argparse
from itertools import permutations
from pathlib import Path

from census import graph


def render(stages):
    edges = graph(stages)
    index = {pair: i for i, pair in enumerate(edges)}
    matchings = [[index[(a, b)] for a, b in enumerate(order)]
                 for order in permutations(range(7, 14))
                 if all((a, b) in index for a, b in enumerate(order))]
    assert len(matchings) == 24
    masks = [sum(1 << i for i in row) for row in matchings]
    packed = [0] * 128
    for vertices in range(1 << 14):
        exterior = sum(1 << i for i, (a, b) in enumerate(edges)
                       if not ((vertices >> a) & (vertices >> b) & 1))
        choice = max(range(len(masks)), key=lambda j: (exterior & masks[j]).bit_count())
        packed[vertices // 128] |= choice << (5 * (vertices % 128))
    def rows(values):
        return '[\n  ' + ',\n  '.join(map(str, values)) + '\n]'
    return ('import Mathlib.Data.Finset.Card\n\nnamespace Checkpoint125.Certificate\n\n'
            '-- Generated from the posted edge list by certificate.py.\n'
            'def pairs : List (Fin 14 × Fin 14) := ' + str(edges) + '\n\n'
            'def matchings : List (List (Fin 21)) := ' + rows(matchings) + '\n\n'
            '-- Each five-bit field selects one of the listed perfect matchings.\n'
            'def packed : List ℕ := ' + rows(packed) + '\n\nend Checkpoint125.Certificate\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', type=Path, required=True)
    args = parser.parse_args()
    print(render(args.stages), end='')


if __name__ == '__main__':
    main()
