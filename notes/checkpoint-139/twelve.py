"""Verify all nine-rectangle families with twelve light labels and enough area for four exceptions."""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from check import compile_program, degrees, lights_output
from inventory import HERE, build_input, maximal_rectangles, require, six_rectangles
from patterns import low_sets
from rectangles import ROWS, bits, covered_rows


def incompatible(first, second):
    r, c = first
    p, q = second
    return not ((ROWS[r] >> q) & (ROWS[p] >> c) & 1)


def five_cells(pool, conflicts, needed=5):
    if needed == 0:
        return ()
    while pool.bit_count() >= needed:
        bit = pool & -pool
        i = bit.bit_length() - 1
        pool ^= bit
        tail = five_cells(pool & conflicts[i], conflicts, needed - 1)
        if tail is not None:
            return (i, *tail)
    return None


def compute(folder):
    board = folder / 'inventory'
    board.write_text(build_input())
    roots = {(p, q): n for p, q, n in low_sets(12) if p.bit_count() + q.bit_count() == 12}
    marked = folder / 'light-sets'
    marked.write_text(''.join(f'{p} {q} {n}\n' for (p, q), n in roots.items()))
    maximum = six_rectangles()
    maximum_set = set(maximum)
    largest = max(a.bit_count() * b.bit_count() for a, b in maximal_rectangles()
                  if (a, b) not in maximum_set)
    cells = [(r, c) for r in range(21) for c in bits(ROWS[r])]
    threshold = len(cells) - 4 * largest
    raw = subprocess.check_output([compile_program('patterns', folder), board, marked, '9', '12',
                                   str(threshold)], text=True)
    conflicts = [sum(1 << k for k, other in enumerate(cells) if incompatible(cell, other))
                 for cell in cells]
    lines, certificates, seen = [], [], set()
    count = Counter()
    for line in raw.splitlines(keepends=True):
        if not line.startswith('FAMILY '):
            lines.append(line)
            continue
        p, q, n, *ids = map(int, line.split()[1:])
        require((p, q) in roots and len(ids) == 9 and ids == sorted(set(ids)) and
                all(0 <= j < len(maximum) for j in ids), 'Invalid nine-rectangle family')
        require(tuple(ids) not in seen, 'Repeated family')
        seen.add(tuple(ids))
        d = degrees(ids, maximum)
        require([sum(1 << i for i, v in enumerate(side) if v <= 2) for side in d] == [p, q],
                'Light labels disagree with the marking')
        covered = covered_rows([maximum[j] for j in ids])
        require(sum(w.bit_count() for w in covered) == n >= threshold, 'Wrong family coverage')
        missing = sum(1 << k for k, (r, c) in enumerate(cells) if not (covered[r] >> c & 1))
        witness = five_cells(missing, conflicts)
        require(witness is not None, 'A residual requires a different completion test')
        points = [cells[k] for k in witness]
        require(len(set(points)) == 5 and all(ROWS[r] >> c & 1 and not (covered[r] >> c & 1)
                for r, c in points) and all(incompatible(a, b) for a, b in combinations(points, 2)),
                'Invalid five-cell witness')
        certificates.append((*ids, *(21*r + c for r, c in points)))
        count[n] += roots[p, q]
    histograms = folder / 'histograms'
    histograms.write_text(''.join(lines))
    distribution = lights_output(histograms, 9, 12, roots)
    require(count == {int(k): n for k, n in distribution['families_by_coverage']['12'].items()
                      if int(k) >= threshold}, 'A family meeting the area threshold was omitted')
    table = ''.join(' '.join(map(str, r)) + '\n' for r in sorted(certificates))
    result = dict(largest_exceptional_maximal_area=largest, minimum_nine_rectangle_coverage=threshold,
                  families_checked_at_representative_markings=len(certificates),
                  physical_families_with_five_cell_witnesses=sum(count.values()),
                  covered_cells_among_certified={str(k): n for k, n in sorted(count.items())},
                  certificates_sha256=sha256(table.encode()).hexdigest(), light_sets=distribution)
    return result, table


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write the computed JSON and TSV into this directory')
    args = parser.parse_args()
    with TemporaryDirectory() as tmp:
        result, table = compute(Path(tmp))
    if args.output:
        args.output.mkdir(exist_ok=True, parents=True)
        (args.output/'twelve.json').write_text(json.dumps(result, indent=2) + '\n')
        (args.output/'twelve-witnesses.tsv').write_text(table)
    else:
        require(result == json.loads((HERE/'twelve.json').read_text()), 'Published counts differ')
        require(table == (HERE/'twelve-witnesses.tsv').read_text(), 'Published five-cell witnesses differ')
    print(result['families_checked_at_representative_markings'], 'representative families,',
          result['physical_families_with_five_cell_witnesses'], 'physical families certified')
