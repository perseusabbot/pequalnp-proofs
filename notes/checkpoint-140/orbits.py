"""Check the four-rectangle orbit partition by marking every physical four-subset."""
import argparse
from hashlib import sha256
import json
from math import comb
from pathlib import Path
from tempfile import TemporaryDirectory

import numpy as np
from replay import anchors, program
from input_data import HERE, geometry, require
from weights import Checker


def check(matrix, directory):
    board, seeds = directory / 'board', directory / 'four'
    board.write_text(geometry())
    roots = anchors(program('anchors', directory), board, 4, seeds)
    checker = Checker(matrix)
    ranks = np.array([[comb(i, j) for i in range(168)] for j in range(1, 5)], dtype=np.int32)
    seen = np.zeros(comb(168, 4), dtype=bool)
    for *ids, multiplicity in roots:
        images = np.sort(np.stack([checker.himage(h) for h in ids]), axis=0)
        indices = np.unique(sum(ranks[j, images[j]] for j in range(4)))
        require(len(indices) == multiplicity and not seen[indices].any(), 'Overlapping orbit or wrong size')
        seen[indices] = True
    require(seen.all(), 'A physical four-subset is missing')
    return dict(representatives=len(roots), physical_subsets=int(seen.sum()),
                group_order=len(checker.group), anchors_sha256=sha256(seeds.read_bytes()).hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('matrix', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    with TemporaryDirectory() as directory:
        receipt = check(args.matrix, Path(directory))
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    else:
        require(receipt == json.loads((HERE / 'orbits.json').read_bytes()), 'Published orbit counts differ')
    print(receipt['physical_subsets'], 'four-subsets marked in', receipt['representatives'], 'disjoint orbits')
