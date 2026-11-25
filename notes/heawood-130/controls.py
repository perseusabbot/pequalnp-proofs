"""Construct optimal star circuits for the four newly exhausted row tests."""
from itertools import combinations

from transport import DIRECT, EDGES, instance


def circuits():
    controls = []
    for mask, vertices in DIRECT:
        s = instance(mask, vertices)
        order = [v for v in range(14) if vertices >> v & 1]
        edges = [(a,b) for a,b in EDGES if (1 << a | 1 << b) in s['positive_rows']]
        centers = next(chosen for k in range(1,len(order)+1) for chosen in combinations(order,k)
                       if all(a in chosen or b in chosen for a,b in edges))
        neighbors = {v:[] for v in centers}
        for a,b in edges:
            v = a if a in centers else b
            neighbors[v].append(b if v==a else a)
        def pack(word):
            return sum(1 << i for i,v in enumerate(order) if word >> v & 1)
        cols = [pack(w) for w in s['signals']]
        pairs = [pack(w) for w in s['positive_rows']]
        ops = []
        def add(op,a,b):
            ops.append([op,a,b])
            return len(cols)+len(ops)-1
        def fold(wires):
            head,*tail = wires
            for w in tail:
                head = add('OR',head,w)
            return head
        def port(v):
            return s['signals'].index(1 << v)
        stars = [add('AND',port(v),fold([port(u) for u in ns])) for v,ns in neighbors.items()]
        last = fold(stars)
        if last != len(cols)+len(ops)-1 or len(ops)!=s['gate_cap']+1:
            raise ValueError('Upper and lower bounds differ')
        for row in range(1 << len(order)):
            wires = [bool(w & row) for w in cols]
            for op,a,b in ops:
                wires.append(wires[a] and wires[b] if op=='AND' else wires[a] or wires[b])
            if wires[-1]!=any(row & p == p for p in pairs):
                raise ValueError('Star circuit fails')
        controls.append(dict(mask=mask, vertices=vertices, vertex_order=order, columns=cols, edges=pairs,
                             gates=ops, minimum=len(ops), assignments=1 << len(order)))
    return controls
