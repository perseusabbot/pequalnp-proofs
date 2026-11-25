"""Exhaust the live input sets and check the thirteen-gate circuit on all rows."""
from collections import Counter
from functools import cache
from itertools import combinations
import json
from pathlib import Path

PRIOR = Path(__file__).resolve().parent.parent / 'heawood-127'


def instance():
    data = json.loads((PRIOR / 'ten_census.json').read_text())['representative_restriction']
    order = data['vertex_order']
    masks = [1 << i for i in range(len(order))]
    def local(vertices):
        return sum(1 << order.index(v) for v in vertices)
    masks += [local(pair) for pair in data['allowed_extra_disjunctions']]
    positive = sorted(map(local, data['missing_edges']))
    def target(row):
        return any(row & edge == edge for edge in positive)
    negative = [r for r in range(1 << len(order)) if not target(r) and
                all(target(r | bit) for bit in masks[:len(order)] if not bit & r)]
    return data, masks, positive, negative


def check_control(data, masks, positive):
    rows = 1 << len(data['vertex_order'])
    for row in range(rows):
        values = [bool(s & row) for s in masks]
        for op, a, b in data['control_gates']:
            assert 0 <= a < len(values) and 0 <= b < len(values) and op in ('AND', 'OR')
            values.append((values[a] and values[b]) if op == 'AND' else (values[a] or values[b]))
        assert values[data['control_output_port']] == any(row & e == e for e in positive)
    return rows


def exhaust(masks, positive, negative, caps=(11, 12)):
    rows = positive + negative
    palette = [sum(1 << i for i, r in enumerate(rows) if mask & r) for mask in masks]
    width = len(negative)
    full = (1 << (len(positive)*width)) - 1
    goal = (1 << len(positive)) - 1

    @cache
    def cover(x):
        neg_off = ((1 << width) - 1) ^ (x >> len(positive))
        return sum(neg_off << (i*width) for i in range(len(positive)) if x & (1 << i))

    def covers(state):
        union = 0
        for x in state:
            union |= cover(x)
        return union

    mandatory = [i for i in range(len(masks)) if covers(palette[:i]+palette[i+1:]) != full]
    optional = [i for i in range(len(masks)) if i not in mandatory]
    supports = []
    for size in range(len(optional)+1):
        for extra in combinations(optional,size):
            group = tuple(sorted(mandatory+list(extra)))
            if covers(palette[i] for i in group) == full:
                supports.append(group)

    def run(cap):
        counts = Counter()
        @cache
        def possible(k, state):
            counts[k] += 1
            if goal in state:
                return True
            if k == 0:
                return False
            for i, x in enumerate(state):
                for j in range(i+1, len(state)):
                    y = state[j]
                    rest = state[:i] + state[i+1:j] + state[j+1:]
                    covered = covers(rest)
                    # A cut introduces a fresh terminal even when its truth
                    # signature coincides with another one. Keep multiplicities.
                    for z in (x & y, x | y):
                        base = covered | cover(z)
                        for kept in ((), (x,), (y,), (x,y)):
                            if len(rest)+len(kept)+1 > k or (base | covers(kept)) != full:
                                continue
                            next_state = tuple(sorted(rest + kept + (z,)))
                            if possible(k-1, next_state):
                                return True
            return False

        found = any(possible(cap,tuple(sorted(palette[i] for i in s)))
                    for s in supports if len(s)<=cap+1)
        return dict(cap=cap, possible=found, distinct_states=sum(counts.values()),
                    states_by_gates_remaining=dict(sorted(counts.items())))

    return supports,[run(k) for k in caps]


def main():
    data,masks,pos,neg=instance()
    rows=check_control(data,masks,pos)
    supports,results=exhaust(masks,pos,neg)
    assert rows==512 and len(pos)==10 and len(neg)==11 and len(supports)==8
    assert all(set(s[:9])==set(range(9)) for s in supports)
    assert all(not r['possible'] for r in results)
    print(json.dumps(dict(positive_rows=pos,maximal_negative_rows=neg,palette_masks=masks,
                          input_supports=supports,search=results,control_gates=len(data['control_gates']),
                          control_assignments=rows,minimum_gates=len(data['control_gates'])),indent=2))


if __name__=='__main__':
    main()
