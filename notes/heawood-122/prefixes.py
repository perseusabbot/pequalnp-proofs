"""Match the posted two-gate representatives to the optimal Heawood star circuits."""
import argparse
from ast import literal_eval
from itertools import combinations, product
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
STAGES = HERE.parents[1] / '3004/check120/controls/HeawoodStages.lean'


def read_inputs(statement, stages):
    text = statement.read_text()
    columns = list(map(int, re.findall(r'\((\d+) : ℕ\)', text[:text.index(']; have x2')])))
    table = text[text.index('([['):text.index(']].getD')]
    keys = list(map(int, re.findall(r'\((\d+) : ℕ\)', table)))
    edges = literal_eval(re.search(r'^def edges.*?:= (\[.+\])$', stages.read_text(), re.M)[1])
    if (len(columns), len(keys), len(edges)) != (14, 65, 21):
        raise ValueError('Unexpected posted instance')
    return columns, keys, edges


def encode(a, b, use_or):
    return a + 64*b + 4096*use_or


def evaluate(gates, input_words):
    wires = input_words[:]
    for code in gates:
        i, j = code % 64, code // 64 % 64
        a = wires[i] if i < len(wires) else 0
        b = wires[j] if j < len(wires) else 0
        wires.append(a | b if code >= 4096 else a & b)
    return wires[-1]


def build(prefix, centers, neighborhoods, pairs):
    """Complete the actual first two gates using one chosen pair per full star."""
    gates, refs = [], {1 << i: i for i in range(14)}
    supports = list(refs)

    def add(a, b, use_or):
        gates.append(encode(a, b, use_or))
        return len(gates) + 13

    for i, j in prefix:
        mask = supports[i] | supports[j]
        refs[mask] = add(i, j, True)
        supports.append(mask)
    triples = []
    for center, (a, b) in zip(centers, pairs):
        (c,) = neighborhoods[center] - {a, b}
        pair = (1 << a) | (1 << b)
        if pair not in refs:
            refs[pair] = add(a, b, True)
        triple = pair | (1 << c)
        if triple not in refs:
            refs[triple] = add(refs[pair], c, True)
        triples.append(refs[triple])
    stars = [add(c, t, False) for c, t in zip(centers, triples)]
    acc = stars[0]
    for star in stars[1:]:
        acc = add(acc, star, True)
    if len(gates) != 27:
        raise ValueError('Incorrect star schedule')
    return gates


def families(keys, neighbors):
    prefixes = []
    for i, key in enumerate(keys):
        p = [(0, key // 225 % 14), (key % 225 // 15, key % 15)]
        supports = [1 << v for v in range(14)]
        for a, b in p:
            supports.append(supports[a] | supports[b])
        prefixes.append((i, p, *supports[-2:]))
    for centers in (range(7), range(7, 14)):
        triples = [sum(1 << v for v in neighbors[c]) for c in centers]
        for pairs in product(*(combinations(sorted(neighbors[c]), 2) for c in centers)):
            library = set(triples) | {(1 << a) | (1 << b) for a, b in pairs}
            for i, prefix, first, second in prefixes:
                if first == second or first not in library or second not in library:
                    continue
                yield i, prefix, centers, pairs


def classify(statement, stages):
    columns, keys, edges = read_inputs(statement, stages)
    raw = [sum(1 << i for i in range(1 << 14) if i >> v & 1) for v in range(14)]
    target, neighbors = 0, [set() for _ in raw]
    for u, v in edges:
        target |= raw[u] & raw[v]
        neighbors[u].add(v)
        neighbors[v].add(u)
    counts = [0] * 65
    controls = {}
    for i, prefix, centers, pairs in families(keys, neighbors):
        counts[i] += 1
        if i not in controls:
            codes = build(prefix, centers, neighbors, pairs)
            if evaluate(codes, columns) != 2097151 or evaluate(codes, raw) != target:
                raise ValueError(f'Invalid control at index {i}')
            controls[i] = dict(index=i, key=keys[i], ports=prefix, codes=codes)
    return dict(possible_indices=sorted(controls),
                layouts_per_index=counts, tested_bottom_libraries=2*3**7,
                controls=[controls[i] for i in sorted(controls)], assignments_per_control=2**14)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--statement', type=Path, default=HERE/'statement.txt')
    parser.add_argument('--stages', type=Path, default=STAGES)
    args = parser.parse_args()
    print(json.dumps(classify(args.statement, args.stages), indent=2))
