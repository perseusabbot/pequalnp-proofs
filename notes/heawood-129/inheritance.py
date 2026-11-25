"""Apply established local obstructions to larger lost-edge sets."""
from itertools import permutations

from instances import EDGES, ENDS, disjoint_matching, endpoints, instance


def maps():
    neighbors = [set() for _ in range(14)]
    for a,b in EDGES:
        neighbors[a].add(b)
        neighbors[b].add(a)
    vertex_of_neighbors = {frozenset(ns):v for v,ns in enumerate(neighbors)}
    edge_index = {frozenset(e):i for i,e in enumerate(EDGES)}
    result = []
    for side in (range(7),range(7,14)):
        for first in permutations(side):
            second = [vertex_of_neighbors.get(frozenset(first[x] for x in neighbors[v])) for v in range(7,14)]
            if None in second:
                continue
            p = tuple([*first,*second])
            if len(set(p))!=14:
                raise ValueError('The vertex map is not bijective')
            action = tuple(edge_index[frozenset((p[a],p[b]))] for a,b in EDGES)
            if len(set(action))!=21:
                raise ValueError('The edge map is not bijective')
            result.append((p,action))
    if len(result)!=336 or len(set(result))!=336:
        raise ValueError('Incorrect symmetry group')
    return result


def move(word, mapping):
    return sum(1 << mapping[i] for i in range(len(mapping)) if word >> i & 1)


def cover_layers(census_layers, screens):
    automorphisms = maps()
    by_mask = {c['representative']:c for c in screens}
    # All earlier losses incident to the sample may be required below. This is
    # only a quick sufficient lookup. Every match is checked on the actual rows.
    lookup = {}
    for source in screens:
        m = source['representative']
        t = source['sample_vertices']
        required = sum(1 << i for i,e in enumerate(ENDS) if m >> i & 1 and t & e)
        slack = source['gate_cap']-t.bit_count()
        for idx,(p,edges) in enumerate(automorphisms):
            key = move(required,edges)
            if key not in lookup or slack>lookup[key][0]:
                lookup[key] = (slack,m,idx)
    eligible = {}
    output = []
    for layer in census_layers:
        proofs = []
        pending = []
        for orbit in layer['orbits']:
            m = orbit['representative']
            if m in by_mask:
                proofs.append(dict(representative=m,size=orbit['size'],direct=True))
                continue
            slack = 26-(21-m.bit_count())-len(disjoint_matching(m))-endpoints(m).bit_count()
            if slack not in eligible:
                eligible[slack] = [(key,s,idx) for key,(space,s,idx) in lookup.items() if space>=slack]
            hit = next(((s,idx) for key,s,idx in eligible[slack] if m & key == key),None)
            if hit is None:
                pending.append(dict(representative=m,size=orbit['size']))
                continue
            source_mask,idx = hit
            source = by_mask[source_mask]
            p,_ = automorphisms[idx]
            t = move(source['sample_vertices'],p)
            actual = instance(m,t)
            def moved(field):
                return {move(n,p) for n in source[field]}
            if (actual['gate_cap']>source['gate_cap']
                    or not set(actual['signals'])<=moved('signals')
                    or not moved('positive_rows')<=set(actual['positive_rows'])
                    or set(actual['negative_rows'])!=moved('negative_rows')):
                raise ValueError('Transferred circuit specification is not a relaxation')
            proofs.append(dict(representative=m,size=orbit['size'],source=source_mask,
                               permutation=list(p),projected_budget=actual['gate_cap']))
        unresolved = sum(q['size'] for q in pending)
        if unresolved+sum(q['size'] for q in proofs)!=layer['candidates']:
            raise ValueError('Orbit accounting mismatch')
        output.append(dict(losses=layer['losses'],checked=layer['checked'],candidates=layer['candidates'],
                           sorted_masks_sha256=layer['sorted_masks_sha256'],representatives=len(layer['orbits']),
                           excluded=layer['candidates']-unresolved,remaining=unresolved,
                           certificates=proofs,open_representatives=pending))
    return output
