"""Regenerate the two eight-gate lower-bound certificates and their controls."""
import argparse
from collections import Counter
from itertools import combinations, permutations
import json


def model(claw):
    if claw:
        size = 7
        edges = [(0, i) for i in range(1, 4)] + [(i, i+3) for i in range(1, 4)]
        signals = [1 << i for i in range(size)]
        signals.extend(sum(1 << i for i in group)
                       for length in (2, 3) for group in combinations(range(4, 7), length))
    else:
        size = 6
        edges = [(i, (i+1) % size) for i in range(size)]
        signals = [1 << i for i in range(size)]
    return size, edges, signals


def switched_rows(paths, size, signals, target, gate):
    for outer1, first, second, outer2 in paths:
        path = sum(1 << i for i in (outer1, first, second, outer2))
        for fixed in range(1 << size):
            if fixed & path:
                continue
            rows = [fixed | (h * ((1 << outer1) | (1 << outer2))) | ((i & 1) << first) |
                    (((i >> 1) & 1) << second) for h in range(2) for i in range(4)]
            if [int(target(r)) for r in rows] != [0, 0, 0, 1, 0, 1, 1, 1]:
                continue
            def constant_in_each_setting(values):
                return len(set(values[:4])) == len(set(values[4:])) == 1
            if not constant_in_each_setting([gate(r) for r in rows]):
                continue
            if all(constant_in_each_setting([bool(s & r) for r in rows])
                   for s in signals if s not in (1 << first, 1 << second)):
                return 1 << first, 1 << second, rows
    raise ValueError('Missing switch certificate for a six-label case')


def build(claw):
    size, edges, signals = model(claw)
    positives = sorted((1 << a) | (1 << b) for a, b in edges)
    def target(row):
        return any(row & mask == mask for mask in positives)
    negatives = [r for r in range(1 << size) if not target(r) and
                 all(target(r | (1 << v)) for v in range(size) if not r & (1 << v))]
    # If every other allowed signal transfers from the positive to the negative
    # row, the indicated singleton must occur in any monotone representation.
    witnesses = [[(p, n) for p in positives for n in negatives
                  if all(not (s & p) or (s & n) or s == 1 << i for s in signals)]
                 for i in range(size)]
    adjacency = {frozenset(e) for e in edges}
    paths = [(a, b, c, d) for a, b, c, d in permutations(range(size), 4)
             if [frozenset(e) in adjacency for e in ((a,b),(b,c),(c,d),(a,c),(b,d),(a,d))]
             == [True, True, True, False, False, False]]
    records = []
    for x, y in combinations(signals, 2):
        for is_or in (False, True):
            def gate(row):
                a, b = bool(x & row), bool(y & row)
                return (a or b) if is_or else (a and b)
            forced = []
            for i, pairs in enumerate(witnesses):
                witness = next(((p, n) for p, n in pairs if not gate(p) or gate(n)), None)
                if witness:
                    forced.append((1 << i, *witness))
            if len(forced) < 6:
                raise ValueError('The separating assignments do not force six labels')
            switch = switched_rows(paths, size, signals, target, gate) if len(forced) == 6 else (0, 0, [])
            records.append((x, y, is_or, forced, switch))
    return signals, positives, records


def lean_list(items):
    return '[' + ','.join(map(str, items)) + ']'


def render(both):
    lines = ['import Mathlib.Data.Nat.Basic', '', 'namespace Checkpoint127.Small', '',
             'structure Case where', '  x : ℕ', '  y : ℕ', '  isOr : Bool',
             '  needed : List (ℕ × Fin 128 × Fin 128)', '  first : ℕ', '  second : ℕ',
             '  rows : List (Fin 128)', '', 'def palette : Bool → List ℕ']
    for flag, (signals, _, _) in zip(('false', 'true'), both):
        lines.append(f'  | {flag} => {lean_list(signals)}')
    lines.append('def positives : Bool → List ℕ')
    for flag, (_, positive, _) in zip(('false', 'true'), both):
        lines.append(f'  | {flag} => {lean_list(positive)}')
    for name, (_, _, records) in zip(('cycleCases', 'clawCases'), both):
        lines.extend(['', f'def {name} : List Case := ['])
        for x, y, is_or, forced, (a, b, rows) in records:
            proofs = lean_list(['(%d,%d,%d)' % triple for triple in forced])
            lines.append(f'  ⟨{x},{y},{str(is_or).lower()},{proofs},{a},{b},{lean_list(rows)}⟩,')
        lines[-1] = lines[-1][:-1]
        lines.append(']')
    return '\n'.join([*lines, '', 'end Checkpoint127.Small', ''])


def control(claw):
    size, edges, _ = model(claw)
    if claw:
        groups = [(1, 0, 4), (2, 0, 5), (3, 0, 6)]
    else:
        groups = [(0, 1, 5), (2, 1, 3), (4, 3, 5)]
    gates, products = [], []
    for center, a, b in groups:
        gates.append(['OR', a, b])
        gates.append(['AND', center, size+len(gates)-1])
        products.append(size+len(gates)-1)
    gates.append(['OR', products[0], products[1]])
    gates.append(['OR', size+len(gates)-1, products[2]])
    for row in range(1 << size):
        values = [bool(row & (1 << i)) for i in range(size)]
        for op, a, b in gates:
            values.append((values[a] or values[b]) if op == 'OR' else (values[a] and values[b]))
        target = any((row & (1 << u)) and (row & (1 << v)) for u, v in edges)
        if values[-1] != target:
            raise ValueError(f'Incorrect eight-gate control at row {row}')
    return dict(variables=size, truth_rows=1 << size, gates=gates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true', help='print the complete Lean certificate')
    args = parser.parse_args()
    both = [build(k) for k in (False, True)]
    if args.lean:
        print(render(both), end='')
    else:
        print(json.dumps({name: dict(bottom_gates=len(records),
              forced_labels=dict(sorted(Counter(len(r[3]) for r in records).items())), control=control(claw))
              for name, claw, (_, _, records) in zip(('six_cycle','subdivided_claw'), (False, True), both)}, indent=2))


if __name__ == '__main__':
    main()
