"""Check the published residual witnesses using only the upstream matrix and two text files."""
import argparse
from collections import Counter
from functools import reduce
from hashlib import sha256
from heapq import nlargest
from operator import and_, or_
from pathlib import Path
import json
import re


def check(upstream, certificates):
    source = upstream.read_bytes()
    declared = re.search(rb'^def incidence : List Nat := \[([0-9, ]+)\]$', source, re.M)
    if declared is None:
        raise ValueError('Could not find the upstream matrix')
    full = (1 << 21) - 1
    rows = [full ^ int(s) for s in declared.group(1).split(b',')]
    assert len(rows) == 21 and all(w.bit_count() == 16 for w in rows)
    intersections = {full}
    for row in rows:
        intersections.update({w & row for w in intersections})
    boxes = []
    for columns in intersections - {0}:
        used = [r for r, row in enumerate(rows) if row & columns == columns]
        if not used:
            continue
        assert reduce(and_, (rows[r] for r in used)) == columns
        boxes.append((sum(1 << r for r in used), columns, sum(columns << (21*r) for r in used)))
    boxes.sort()
    maximum = [w for a, b, w in boxes if a.bit_count() == b.bit_count() == 6]
    others = [w for a, b, w in boxes if a.bit_count() * b.bit_count() != 36]
    assert len(boxes) == 25235 and len(maximum) == 168 and len(others) == 25067
    all_zeros = sum(row << (21*r) for r, row in enumerate(rows))
    coverage, best_one, area_upper = Counter(), Counter(), Counter()
    seen = set()
    for line in certificates.read_text().splitlines():
        ids = list(map(int, line.split()))
        assert len(ids) == 14
        family, markers = ids[:9], ids[9:]
        assert family == sorted(set(family)) and all(0 <= j < len(maximum) for j in family)
        assert tuple(family) not in seen
        seen.add(tuple(family))
        covered = reduce(or_, (maximum[i] for i in family))
        missing = all_zeros & ~covered
        f = sum(1 << c for c in markers)
        assert len(set(markers)) == 5 and (missing & f) == f and f.bit_count() == 5
        assert all((b & f).bit_count() <= 1 for _, _, b in boxes)
        gain = nlargest(4, ((b & missing).bit_count() for b in others))
        coverage[covered.bit_count()] += 1
        best_one[gain[0]] += 1
        area_upper[covered.bit_count() + sum(gain)] += 1
    assert sum(coverage.values()) == 126 and coverage == {224: 54, 225: 72}
    return dict(matrix_source_sha256=sha256(source).hexdigest(),
                witnesses_sha256=sha256(certificates.read_bytes()).hexdigest(),
                maximal_rectangles=len(boxes), cells_in_each_witness=5, representative_witnesses=len(seen),
                tests_of_one_maximal_rectangle_against_one_witness=len(boxes)*len(seen),
                maximum_witness_cells_in_any_single_rectangle=1, nine_rectangle_coverage=dict(coverage),
                largest_single_exceptional_gain=dict(best_one), four_largest_gains_plus_original_coverage=dict(area_upper))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('upstream_lean', type=Path)
    p.add_argument('witnesses_tsv', type=Path)
    args = p.parse_args()
    print(json.dumps(check(args.upstream_lean, args.witnesses_tsv), indent=2, sort_keys=True))
