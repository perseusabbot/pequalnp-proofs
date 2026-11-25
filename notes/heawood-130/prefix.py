"""Independently verify explicit short-prefix and row-substitution certificates."""
from collections import Counter
from functools import cache

from transport import fano_actions, instance, moved, source_screens


def check(ok, message):
    if not ok:
        raise ValueError(message)


@cache
def sources():
    return {c['representative']: c for c in source_screens()}


@cache
def symmetries():
    return [perm for _, perm in fano_actions()[0]]


@cache
def geometry(source, symmetry):
    c = sources()[source]
    perm = symmetries()[symmetry]
    def transport(key):
        return tuple(sorted(moved(w, perm) for w in c[key]))
    return (moved(c['sample_vertices'], perm), transport('signals'), transport('positive_rows'),
            transport('negative_rows'), c['gate_cap'] + 1)


def gate(op, a, b):
    return a | b if op else a & b


class PrefixProblem:
    def __init__(self, mask, vertices, cap):
        self.mask, self.vertices, self.cap = mask, vertices, cap
        row = instance(mask, vertices)
        self.inputs = row['signals']
        self.positive = row['positive_rows']
        self.negative = row['negative_rows']
        self.rows = self.positive + self.negative
        self.n = len(self.inputs)
        self.pos = (1 << len(self.positive)) - 1
        self.neg = ((1 << len(self.rows)) - 1) ^ self.pos
        self.base = [self.column(s) for s in self.inputs]
        self.row_number = {r: i for i, r in enumerate(self.rows)}
        self.group = set()
        for perm in symmetries():
            ports = [moved(s, perm) for s in self.inputs]
            if (set(ports) == set(self.inputs) and {moved(p, perm) for p in self.positive} == set(self.positive)
                    and {moved(n, perm) for n in self.negative} == set(self.negative)):
                self.group.add(tuple(self.inputs.index(s) for s in ports))
        check(self.group and len(self.row_number) == len(self.rows), 'Invalid root test')
        self.counts = Counter()
        self.depths = Counter()
        self.used_sources = Counter()

    def column(self, s):
        return sum(1 << i for i, r in enumerate(self.rows) if s & r)

    def indispensable(self, wires, ops):
        # Every prefix output not consumed by another prefix gate must feed the
        # suffix in a minimum circuit. A unique row distinction forces its label too.
        required = set(range(self.n, len(wires))) - {k for _, a, b in ops for k in (a, b)}
        active = [sum(1 << k for k, col in enumerate(wires) if col >> r & 1)
                  for r in range(len(self.rows))]
        for p in active[:len(self.positive)]:
            for n in active[len(self.positive):]:
                diff = p & ~n
                if diff.bit_count() == 1:
                    required.add(diff.bit_length()-1)
        return required

    def children(self, wires, group):
        check(self.pos not in wires, 'The root test already has a solution')
        for a in range(len(wires)):
            for b in range(a):
                def image_at(perm, i):
                    return perm[i] if i < self.n else i
                images = {tuple(sorted((image_at(perm, a), image_at(perm, b)))) for perm in group}
                if (b, a) != min(images):
                    continue
                for op in (0, 1):
                    val = gate(op, wires[a], wires[b])
                    check(val != self.pos, 'An enumerated operation solves the root test')
                    # A minimum circuit cannot create a column replaceable by a
                    # constant or an old column while preserving both row signs.
                    if not val & self.pos or val & self.neg == self.neg:
                        continue
                    if any((val & self.pos) & ~old == 0 and (old & self.neg) & ~val == 0 for old in wires):
                        continue
                    subgroup = {perm for perm in group if {image_at(perm, a), image_at(perm, b)} == {a,b}}
                    yield (op, a, b), val, subgroup

    def leaf(self, cert, wires, ops):
        source, symmetry, new_ports, lifts = cert
        t, palette, ps, ns, lower = geometry(source, symmetry)
        check(not t & ~self.vertices and set(ps) <= set(self.positive), 'Positive row is missing')
        check(len(ns) == len(lifts) and len(ops) == len(new_ports), 'Incorrect certificate width')
        ports = [s & t if any(s & p for p in ps) else 0 for s in self.inputs] + new_ports
        check(set(ports) <= set(palette) | {0, -1}, 'Unlicensed replacement input')
        def on(port, row):
            return port == -1 or bool(port & row)
        for p in ps:
            index = self.row_number[p]
            check(all(not (v >> index & 1) or on(m, p) for m, v in zip(ports, wires)),
                  'A positive implication fails')
        for n, r in zip(ns, lifts):
            check(r in self.negative and r & t == n, 'Incorrect negative row lift')
            index = self.row_number[r]
            check(all(not on(m, n) or v >> index & 1 for m, v in zip(ports, wires)),
                  'A negative implication fails')
        needed = self.indispensable(wires, ops)
        dropped = sum(ports[i] in (0, -1) for i in needed)
        check(len(ops) + dropped + lower > self.cap, 'Gate count fails at this leaf')
        self.depths[len(ops)] += 1
        self.used_sources[source] += 1

    def audit(self, cert):
        witnesses = cert['witnesses']
        seen = set()
        def visit(tree, wires, ops, group):
            check(self.pos not in wires, 'A shorter solution exists')
            if type(tree) is int:
                check(0 <= tree < len(witnesses), 'Unknown witness')
                self.leaf(witnesses[tree], wires, ops)
                seen.add(tree)
                return
            check(len(ops) < self.cap, 'Unwitnessed gate cap')
            self.counts['prefixes'] += 1
            cases = {tuple(row[:3]):row[3] for row in tree}
            check(len(cases) == len(tree), 'Duplicate branch')
            for op, val, group2 in self.children(wires, group):
                check(op in cases, 'A possible minimum-circuit gate is missing')
                visit(cases.pop(op), wires + [val], ops + [op], group2)
            check(not cases, 'Spurious branch')
        visit(cert['tree'], self.base, [], self.group)
        check(seen == set(range(len(witnesses))), 'Unused witness')
        return dict(mask=self.mask, vertices=self.vertices, cap=self.cap, symmetries=len(self.group),
                    branching_prefixes=self.counts['prefixes'], leaves=sum(self.depths.values()),
                    depths=dict(sorted(self.depths.items())), source_counts=dict(sorted(self.used_sources.items())))
