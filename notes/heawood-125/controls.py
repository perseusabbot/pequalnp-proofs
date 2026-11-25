"""Check a correct circuit at each possible Heawood pruning loss count."""
import argparse
import json
from pathlib import Path
import re

from census import graph


def construct(edges, losses):
    gates = []
    def gate(a, b, is_or):
        gates.append(a + 64*b + 4096*int(is_or))
        return 13 + len(gates)
    def join(ports):
        root, *rest = ports
        for port in rest:
            root = gate(root, port, True)
        return root

    # Split at most one of the seven three-edge stars.
    ordered = sorted(range(21), key=lambda i: (edges[i][1], edges[i][0]))
    missing = set(ordered[:losses])
    removed, kept = [], []
    for center in range(7, 14):
        for group, ports in ((True, removed), (False, kept)):
            operands = [a for i, (a, b) in enumerate(edges) if b == center and (i in missing) == group]
            if operands:
                ports.append(gate(center, join(operands), False))
    if removed:
        root = join(removed)
        kept.append(gate(root, root, False))
    output = join(kept)
    assert output == 13 + len(gates)
    return gates, sorted(missing)


def evaluate(gates, inputs):
    values = [(x, x, False) for x in inputs]
    for q in gates:
        a, b = q % 64, (q // 64) % 64
        if not (0 <= q < 8192 and max(a, b) < len(values)):
            raise ValueError('Invalid gate code')
        x, px, ax = values[a]
        y, py, ay = values[b]
        if q >= 4096:
            values.append((x | y, px | py, ax or ay))
        else:
            values.append((x & y, 0 if ax or ay else px & py, True))
    return values[-1][:2]


def verify(edges, statement):
    packed = [int(n) for n in re.findall(r'\((\d+) : ℕ\)', statement.read_text().split(']; have x2', 1)[0])]
    assert len(packed) == 14 and max(packed).bit_length() == 58
    truth = [sum(1 << row for row in range(1 << 14) if row & (1 << v)) for v in range(14)]
    cases = []
    for m in range(22):
        codes, missing = construct(edges, m)
        assert len(codes) == (27 if m == 0 else 28 + int(m % 3 != 0))
        for inputs in (truth, packed):
            full = pruned = 0
            for i, (x, y) in enumerate(edges):
                full |= inputs[x] & inputs[y]
                if i not in missing:
                    pruned |= inputs[x] & inputs[y]
            if inputs is packed and full != 2097151:
                raise ValueError('Packed target differs from the posted evaluator')
            if evaluate(codes, inputs) != (full, pruned):
                raise ValueError(f'Circuit for {m} lost edges failed')
        cases.append(dict(losses=m, gate_count=len(codes), codes=codes, lost_edge_indices=missing))
    return dict(assignments_per_circuit=16384, packed_rows=58, cases=cases)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stages', required=True, type=Path)
    p.add_argument('--statement', required=True, type=Path)
    args = p.parse_args()
    print(json.dumps(verify(graph(args.stages), args.statement), indent=2))


if __name__ == '__main__':
    main()
