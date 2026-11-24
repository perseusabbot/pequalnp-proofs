"""Replay pair separation, the four-gate relaxation, and the staged positive controls."""
import argparse
from ast import literal_eval
from collections import Counter
from functools import cache
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[1]


def read_edges(stages):
    text = re.search(r'^def edges.*? := (\[.+\])$', stages.read_text(), re.M)
    edges = literal_eval(text[1])
    if len(set(edges)) != 21 or any(not (0 <= a < 7 <= b < 14) for a, b in edges):
        raise ValueError('Expected the 21 oriented Heawood edges')
    return edges


def subsets(mask):
    value = mask
    while value:
        yield value
        value = (value - 1) & mask
    yield 0


def separate(edges):
    positives = [(1 << a) | (1 << b) for a, b in edges]
    singletons = [1 << v for v in range(14)]
    negatives = singletons + [(1 << a) | (1 << b) for a, b in combinations(range(14), 2)
                               if ((1 << a) | (1 << b)) not in positives]
    sizes = Counter()
    rows = []
    for i, j in combinations(range(21), 2):
        neighbors = [0] * 14
        for k, (u, v) in enumerate(edges):
            if k not in (i, j):
                neighbors[u] |= 1 << v
                neighbors[v] |= 1 << u
        regular = set(singletons)
        for neighborhood in neighbors:
            regular.update(subsets(neighborhood))
        shared = [s for s in regular if s & positives[i] and s & positives[j]]
        witness = next(z for z in negatives if all(s & z for s in shared))
        if any(e & witness == e for e in positives):
            raise ValueError('A purported negative input contains an edge')
        sizes[witness.bit_count()] += 1
        rows.append(dict(edges=[i, j], negative_mask=witness, common_signals=len(shared)))
    return dict(pairs=len(rows), witness_sizes=dict(sorted(sizes.items())), witnesses=rows)


def five_centers(edges):
    seen = set()
    classes = Counter()
    for centers in combinations(range(14), 5):
        lost = tuple(i for i, (a, b) in enumerate(edges) if a not in centers and b not in centers)
        if len(lost) != 6:
            continue
        if lost in seen:
            raise ValueError('The same omission has two qualifying five-center sets')
        seen.add(lost)
        neighbors = {}
        for i in lost:
            a, b = edges[i]
            neighbors.setdefault(a, set()).add(b)
            neighbors.setdefault(b, set()).add(a)
        pending = set(neighbors)
        components = []
        while pending:
            component = {pending.pop()}
            wave = set(component)
            while wave:
                following = {v for u in wave for v in neighbors[u]} & pending
                component.update(following)
                pending.difference_update(following)
                wave = following
            components.append(sorted(len(neighbors[v]) for v in component))
        if sorted(components) == [[1, 1, 2]]*3:
            name = 'three disjoint two-edge paths'
        elif components == [[1, 1, 1, 1, 2, 3, 3]]:
            a, b = [v for v in neighbors if len(neighbors[v]) == 3]
            if b in neighbors[a] or len(neighbors[a] & neighbors[b]) != 1:
                raise ValueError('The two star centers must share one leaf')
            name = 'two three-edge stars sharing one leaf'
        else:
            raise ValueError('Unexpected six-edge graph')
        classes[name] += 1
    return dict(five_subsets_examined=2002, distinct_omissions=len(seen), classes=dict(sorted(classes.items())))


def shape_bounds():
    # Interpret every formula as a 256-row truth table. A monotone function has
    # one minimal DNF term per inclusion-minimal true assignment.
    variables = [sum(1 << x for x in range(256) if x & (1 << i)) for i in range(8)]

    @cache
    def terms(table):
        nonminimal = 0
        for i, var in enumerate(variables):
            nonminimal |= (table << (1 << i)) & var
        return (table & ~nonminimal).bit_count()

    def supply(pure, pool, cut, value):
        return pure, pool | {old | value for old in pool}, cut

    states = {(frozenset(), frozenset({0}), False)}
    rows = []
    for k in range(5):
        cut_states = [pool for _, pool, cut in states if cut]
        largest = max((terms(value) for pool in cut_states for value in pool), default=0)
        rows.append(dict(gates=k, states=len(states), with_nested=len(cut_states), max_terms=largest))
        if k == 4:
            break
        following = set()
        for pure, pool, cut in states:
            left = pure | {variables[2*k]}
            right = pure | {variables[2*k+1]}
            for a in left:
                following.add(supply(pure, pool, cut, a))
                for b in right:
                    following.add((pure | {a | b}, pool, cut))
                    following.add(supply(pure, pool, cut, a & b))
            for a in pool:
                for b in left | pool:
                    following.add(supply(pure, pool, True, a & b))
        states = following
    return rows


def packed_gate(a, b, is_or=False):
    return a + 64*b + 4096*int(is_or)


def control_gates(first_stages, subset):
    gates = list(first_stages)
    selected = [28+i for i in range(7) if subset & (1 << i)]
    others = [28+i for i in range(7) if not subset & (1 << i)]

    def join(ports):
        root = ports[0]
        for port in ports[1:]:
            gates.append(packed_gate(root, port, True))
            root = len(gates)+13
        return root

    root = join(selected)
    gates.append(packed_gate(root, root))
    join([len(gates)+13, *others])
    return gates


def evaluate(codes, inputs, cut):
    wires = list(inputs)
    has_and = [False]*len(wires)
    nested = []
    for index, code in enumerate(codes):
        a, b = code % 64, code // 64 % 64
        if code >= 8192 or max(a, b) >= len(wires):
            raise ValueError('A control has an invalid operand')
        inherited = has_and[a] or has_and[b]
        if code >= 4096:
            value = wires[a] | wires[b]
        else:
            if inherited:
                nested.append(index)
            value = 0 if inherited and cut else wires[a] & wires[b]
        has_and.append(inherited or code < 4096)
        wires.append(value)
    return wires[-1], nested


def controls(edges, prefixes, statement):
    rows = json.loads(prefixes.read_bytes())['controls']
    text = statement.read_text().split(']; have x2', 1)[0]
    packed = [int(n) for n in re.findall(r'\((\d+) : ℕ\)', text)]
    full = [sum(1 << x for x in range(16384) if x & (1 << i)) for i in range(14)]
    if len(packed) != 14 or max(packed).bit_length() != 58:
        raise ValueError('Unexpected packed desk inputs')
    cases = []
    distribution = Counter()
    for row in rows:
        for subset in range(1, 128):
            codes = control_gates(row['codes'][:21], subset)
            if len(codes) != 28 or codes[:2] != row['codes'][:2]:
                raise ValueError('Wrong length or prescribed opening')
            missing = [i for i, (_, v) in enumerate(edges) if subset & (1 << (v-7))]
            for inputs in (packed, full):
                truth = kept = 0
                for i, (u, v) in enumerate(edges):
                    signal = inputs[u] & inputs[v]
                    truth |= signal
                    if i not in missing:
                        kept |= signal
                for prune, target in ((False, truth), (True, kept)):
                    value, nested = evaluate(codes, inputs, prune)
                    if value != target or nested != [20+subset.bit_count()]:
                        raise ValueError(f'Invalid control for opening {row["index"]}, subset {subset}')
            cases.append([row['index'], subset, codes, missing])
            distribution[len(missing)] += 1
    encoded = json.dumps(cases, separators=(',', ':')).encode('ascii')
    return dict(gates=28, controls=len(cases), openings=[row['index'] for row in rows],
                assignments_per_control=16384, packed_rows=58, loss_counts=dict(sorted(distribution.items())),
                cases_sha256=sha256(encoded).hexdigest())


def result(stages, prefixes, statement):
    edges = read_edges(stages)
    return dict(separation=separate(edges), shapes=shape_bounds(), five_centers=five_centers(edges),
                controls=controls(edges, prefixes, statement))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', type=Path, default=RESEARCH/'3004/check120/controls/HeawoodStages.lean')
    parser.add_argument('--prefixes', type=Path, default=RESEARCH/'check122/heawood/prefixes.json')
    parser.add_argument('--statement', type=Path, default=RESEARCH/'check122/heawood/statement.txt')
    args = parser.parse_args()
    print(json.dumps(result(args.stages, args.prefixes, args.statement), indent=2))


if __name__ == '__main__':
    main()
