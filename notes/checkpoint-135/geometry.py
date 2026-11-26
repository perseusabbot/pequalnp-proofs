"""Reconstruct the board, its maximal rectangles, and the three prime-order quotients."""
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'checkpoint-134'))
from verify import (DATA, ROWS, bits, check_cover, maximal_rectangles, permute,
                    quotient, require, union)

ACTIONS = json.loads((HERE / 'actions.json').read_text())
NAMES = ('triangle3', 'homology3')
IDENTITY = bytes(range(42))


def axes(name):
    if name == 'five':
        d = DATA['order_five']
        return d['row_permutation'], d['column_permutation'], 5
    d = ACTIONS[name]
    return d['rows'], d['columns'], 3


def group():
    p, q, _ = axes('five')
    generators = [
        [(i+1) % 21 for i in range(21)] + [21+(i+1) % 21 for i in range(21)],
        p + [21+i for i in q],
        [2*i % 21 for i in range(21)] + [21+(2*i+7) % 21 for i in range(21)],
        [21+(-i) % 21 for i in range(21)] + [(-i) % 21 for i in range(21)],
    ]
    tables = []
    for g in generators:
        require(sorted(g) == list(IDENTITY), 'Invalid group generator')
        for i in range(21):
            for j in range(21):
                a, b = sorted((g[i], g[j+21]))
                require(a < 21 <= b and ROWS[a] >> (b-21) & 1 == ROWS[i] >> j & 1,
                        'Generator changes a board entry')
        tables.append(bytes.maketrans(IDENTITY, bytes(g)))
    elements = [IDENTITY]
    seen = {IDENTITY}
    for g in elements:
        for t in tables:
            other = g.translate(t)
            if other not in seen:
                seen.add(other)
                elements.append(other)
    require(len(elements) == 241920, 'Unexpected group order')
    return elements


def normalizer(elements, p, q):
    h = bytes(p + [21+i for i in q])
    require(h in elements, 'The subgroup generator is outside the enumerated group')
    table = bytes.maketrans(IDENTITY, h)
    square = bytes.maketrans(IDENTITY, h.translate(table))
    require(h.translate(square) == IDENTITY and h != IDENTITY, 'Expected order three')
    return [g for g in elements
            if (gh := h.translate(bytes.maketrans(IDENTITY, g))) == g.translate(table)
            or gh == g.translate(square)]


def boundary_points(name, maximal):
    p, q, period = axes(name)
    cells, fixed, _ = quotient(maximal, p, q, period)
    fixed_union = union(w for _, w in fixed)
    return [c for i, c in enumerate(cells) if not (fixed_union >> i & 1)]
