"""Reconstruct maximum rectangles, local cover patterns, and normalized search cases."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'checkpoint-136'))
from plane import BOARD, ROWS, bits, group
from geometry import maximal_rectangles, require
from subgroups import perm_mask

COLS = [sum(1 << i for i in range(21) if ROWS[i] >> j & 1) for j in range(21)]


def six_rectangles():
    """Enumerate six row labels independently of the maximal-rectangle closure."""
    boxes = []
    for rows in combinations(range(21), 6):
        common = BOARD
        for r in rows:
            common &= ROWS[r]
        if common.bit_count() >= 6:
            a = sum(1 << i for i in rows)
            for cols in combinations(bits(common), 6):
                boxes.append((a, sum(1 << j for j in cols)))
    return sorted(boxes)


def covered_rows(boxes):
    out = [0] * 21
    for a, b in boxes:
        for i in bits(a):
            require(not (b & ~ROWS[i]), 'Illegal rectangle in witness')
            out[i] |= b
    return out


def label_patterns(boxes):
    incidences, triples = [], []
    for label, domain in enumerate([*ROWS, *COLS]):
        axis, point = divmod(label, 21)
        local = {j: box[1-axis] for j, box in enumerate(boxes) if box[axis] >> point & 1}
        require(len(local) == 48, 'A label has the wrong number of maximum rectangles')
        full = []
        for i, j, k in combinations(local, 3):
            covered = local[i] | local[j] | local[k]
            if covered == domain:
                full.append((i, j, k))
            else:
                require(covered.bit_count() <= 14, 'Unexpected fifteen-cell triple')
        require(len(full) == 96, 'Incorrect number of covering triples')
        incidences.append(local)
        triples.append(full)
    return incidences, triples


def case_orbits(patterns, maps):
    """Remove a complete stabilizer orbit of (label, chosen rectangle IDs) at each step."""
    remaining, reps = set(patterns), []
    while remaining:
        label, choice = min(remaining)
        orbit = {(g[label], tuple(sorted(action[h] for h in choice))) for g, action in maps}
        require((label, choice) in orbit and orbit <= remaining, 'Inconsistent stabilizer orbit')
        remaining -= orbit
        reps.append(dict(label=label, ids=list(choice), multiplicity=len(orbit)))
    return reps


def reconstruct():
    boxes = six_rectangles()
    maximal = maximal_rectangles()
    require(len(maximal) == 25235 and len(boxes) == 168, 'Unexpected rectangle inventory')
    require(set(boxes) == {b for b in maximal if b[0].bit_count()*b[1].bit_count() == 36},
            'Maximum rectangle enumerations disagree')
    require(max(a.bit_count()*b.bit_count() for a, b in maximal - set(boxes)) == 28,
            'Unexpected second-largest maximal area')
    incidences, triples = label_patterns(boxes)
    elements = group()
    generators = [perm_mask(g) for g in elements[1:5]]
    words = [a | b << 21 for a, b in boxes]
    index = {w: i for i, w in enumerate(words)}
    require(len({g[0] for g in elements}) == 42, 'The labels are not transitive')

    def actions(stabilizer):
        for g in stabilizer:
            move = perm_mask(g)
            yield g, [index[move(w)] for w in words]

    zero_maps = list(actions(g for g in elements if g[0] == 0))
    require(len(zero_maps) == 5760, 'Wrong label stabilizer')
    local = incidences[0]
    quads = [(0, (i,j,k,l)) for i,j,k,l in combinations(local, 4)
             if local[i] | local[j] | local[k] | local[l] == ROWS[0]]
    pure = case_orbits([(0,t) for t in triples[0]], zero_maps)
    pure += case_orbits(quads, zero_maps)
    require(len(quads) == 7320 and len(pure) == 7, 'Unexpected local pattern orbits')

    remaining = {a | b << 21 for a,b in maximal}
    orbits = []
    while remaining:
        seed = min(remaining)
        orbit, queue = {seed}, [seed]
        for w in queue:
            for move in generators:
                z = move(w)
                if z not in orbit:
                    orbit.add(z)
                    queue.append(z)
        require(orbit <= remaining, 'Generator leaves the maximal-rectangle inventory')
        remaining -= orbit
        a, b = seed & BOARD, seed >> 21
        members = list(bits(seed))
        stabilizer = [g for g in elements if all(seed >> g[i] & 1 for i in members)]
        require(len(orbit)*len(stabilizer) == len(elements), 'Incomplete shape orbit')
        entry = dict(rows=a, cols=b, shape=[a.bit_count(),b.bit_count()],
                     multiplicity=len(orbit), stabilizer=len(stabilizer))
        if (a,b) not in boxes:
            patterns = [(l,t) for l in range(42) if not seed >> l & 1 for t in triples[l]]
            entry['roots'] = case_orbits(patterns, list(actions(stabilizer)))
        orbits.append(entry)

    overlap = None
    for a,b in boxes:
        hist = Counter()
        for c,d in boxes:
            if (a,b) == (c,d):
                continue
            n = (a & c).bit_count()
            require(n == (b & d).bit_count(), 'Different row and column overlap orders')
            hist[n] += 1
        require(overlap is None or hist == overlap, 'Different overlap distribution')
        overlap = hist
    require(all(sum((a >> i & 1)*(b >> j & 1) for a,b in boxes) == 18
                for i, row in enumerate(ROWS) for j in bits(row)), 'Wrong cell frequency')
    return boxes, dict(maximal_count=len(maximal), six_by_six_count=len(boxes), group_order=len(elements),
                       label_incidence=48,cell_incidence=18,pair_overlaps=list(sorted(overlap.items())),
                       covering_triples=96,covering_quadruples=len(quads),pure_roots=pure,shape_orbits=orbits)
