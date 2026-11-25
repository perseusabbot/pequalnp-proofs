"""Encode or check the eleven-gate necessary problem for the ten-loss representative."""
import argparse
from itertools import combinations
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def problem():
    item = json.loads((HERE/'ten_census.json').read_text())['representative_restriction']
    vertices = item['vertex_order']
    index = {v: i for i, v in enumerate(vertices)}
    signals = [1 << i for i in range(len(vertices))]
    signals.extend(sum(1 << index[v] for v in group) for group in item['allowed_extra_disjunctions'])
    positive = sorted(sum(1 << index[v] for v in edge) for edge in item['missing_edges'])
    def target(row):
        return any((row & edge) == edge for edge in positive)
    negative = [row for row in range(1 << len(vertices)) if not target(row) and
                all(target(row | (1 << i)) for i in range(len(vertices)) if not (row >> i) & 1)]
    return item, signals, positive, negative


class Encoding:
    def __init__(self, signals, positive, negative, gate_count):
        self.variables = 0
        self.clauses = []
        self.gates = []
        rows = positive + negative
        wires = [[bool(row & signal) for row in rows] for signal in signals]
        for _ in range(gate_count):
            left = self.selector(len(wires))
            right = self.selector(len(wires))
            is_or = self.fresh()
            self.gates.append((is_or, left, right))
            # Sort these two operand indices. AND and OR are commutative.
            # Equal operands and unused earlier gates are allowed.
            for i, selected in enumerate(left):
                for other in right[:i]:
                    self.clauses.append([-selected, -other])
            output = []
            for r in range(len(rows)):
                a, b, z = self.fresh(), self.fresh(), self.fresh()
                for i, wire in enumerate(wires):
                    self.select_value(left[i], a, wire[r])
                    self.select_value(right[i], b, wire[r])
                self.clauses.extend([[-is_or,-a,z],[-is_or,-b,z],[-is_or,a,b,-z],
                                     [is_or,a,-z],[is_or,b,-z],[is_or,-a,-b,z]])
                output.append(z)
            wires.append(output)
        self.clauses.extend([[z if r < len(positive) else -z] for r, z in enumerate(wires[-1])])

    def fresh(self):
        self.variables += 1
        return self.variables

    def selector(self, count):
        choices = [self.fresh() for _ in range(count)]
        self.clauses.append(choices)
        self.clauses.extend([[-a, -b] for a, b in combinations(choices, 2)])
        return choices

    def select_value(self, select, value, source):
        if isinstance(source, bool):
            self.clauses.append([-select, value if source else -value])
        else:
            self.clauses.extend([[-select, -value, source], [-select, value, -source]])

    def pin(self, gates):
        if len(self.gates) != len(gates):
            raise ValueError('The control has a different gate count')
        for (op, left, right), (kind, a, b) in zip(self.gates, gates):
            a, b = sorted((a, b))
            self.clauses.extend([[op if kind == 'OR' else -op], [left[a]], [right[b]]])

    def write(self, path):
        with path.open('w') as out:
            print('p cnf', self.variables, len(self.clauses), file=out)
            for clause in self.clauses:
                print(*clause, 0, file=out)

    def decode(self, model):
        if 's SATISFIABLE' not in model.splitlines():
            raise ValueError('A SATISFIABLE result and model are required')
        literals = {int(x) for line in model.splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)}
        if any(-x in literals for x in literals) or not all(any(x in literals for x in c) for c in self.clauses):
            raise ValueError('The SAT model does not satisfy the encoded clauses')
        def chosen(options):
            hits = [i for i, x in enumerate(options) if x in literals]
            if len(hits) != 1:
                raise ValueError('Invalid operand selection')
            return hits[0]
        return [['OR' if op in literals else 'AND', chosen(left), chosen(right)] for op, left, right in self.gates]


def verify(gates, item, signals, positive):
    vertices = len(item['vertex_order'])
    for row in range(1 << vertices):
        values = [bool(row & s) for s in signals]
        for op, a, b in gates:
            if not 0 <= a < len(values) or not 0 <= b < len(values):
                raise ValueError('An operand is unavailable')
            values.append((values[a] or values[b]) if op == 'OR' else (values[a] and values[b]))
        if values[-1] != any((row & mask) == mask for mask in positive):
            raise ValueError(f'Incorrect output on assignment {row}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gates', type=int, default=11)
    parser.add_argument('--cnf', type=Path, help='write DIMACS clauses')
    parser.add_argument('--model', type=Path, help='verify and decode a DIMACS SAT model')
    parser.add_argument('--pin-control', action='store_true', help='fix the selectors to the 13-gate positive control')
    args = parser.parse_args()
    if args.gates < 1:
        parser.error('--gates must be positive')
    item, signals, positive, negative = problem()
    encoding = Encoding(signals, positive, negative, args.gates)
    if args.pin_control:
        encoding.pin(item['control_gates'])
    if args.cnf:
        encoding.write(args.cnf)
    report = dict(gates=args.gates, inputs=len(signals), positive_rows=len(positive), maximal_negative_rows=len(negative),
                  cnf_variables=encoding.variables, cnf_clauses=len(encoding.clauses), pinned_control=args.pin_control)
    if args.model:
        gates = encoding.decode(args.model.read_text())
        verify(gates, item, signals, positive)
        report.update(circuit=gates, checked_assignments=item['induced_assignments'])
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
