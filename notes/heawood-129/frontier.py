"""Audit the orbit cover independently using the Fano plane over F₂³."""
import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from instances import HERE, EDGES, ENDS, endpoints, disjoint_matching, instance


def fano_actions():
    lines = {v:[u for u,w in EDGES if w==v] for v in range(7,14)}
    # Points 0, 1, 2 are noncollinear. On each line the third nonzero vector is
    # the binary sum of the first two.
    points = {0:1,1:2,2:4}
    while len(points)<7:
        before = len(points)
        for triple in lines.values():
            known = [points[u] for u in triple if u in points]
            if len(known)==2:
                unknown = next(u for u in triple if u not in points)
                points[unknown] = known[0] ^ known[1]
        if len(points)==before:
            raise ValueError('Incomplete Fano plane coordinates')
    def dot(a,b):
        return (a & b).bit_count() % 2
    normals = {}
    for v,line in lines.items():
        matches = [n for n in range(1,8) if all(dot(n,points[u])==0 for u in line)]
        if len(matches)!=1:
            raise ValueError('Invalid line coordinates')
        normals[v] = matches[0]
    point_of = {x:v for v,x in points.items()}
    line_of = {y:v for v,y in normals.items()}
    if len(point_of)!=7 or len(line_of)!=7:
        raise ValueError('Coordinates are not bijective')
    edge_id = {frozenset(e):i for i,e in enumerate(EDGES)}
    if any((dot(x,y)==0)!=((v,w) in EDGES) for v,x in points.items() for w,y in normals.items()):
        raise ValueError('Incidence mismatch')
    dual = {**{v:line_of[x] for v,x in points.items()},**{v:point_of[y] for v,y in normals.items()}}
    actions = {}
    for a,b,c in product(range(1,8),repeat=3):
        images = [0,a,b,a^b,c,c^a,c^b,c^b^a]
        if len(set(images))!=8:
            continue
        linear = {v:point_of[images[x]] for v,x in points.items()}
        for v,y in normals.items():
            unique = [z for z in range(1,8) if all(dot(x,y)==dot(images[x],z) for x in range(1,8))]
            if len(unique)!=1:
                raise ValueError('Missing inverse transpose')
            linear[v] = line_of[unique[0]]
        for perm in (linear,{v:dual[w] for v,w in linear.items()}):
            action = tuple(edge_id[frozenset((perm[u],perm[v]))] for u,v in EDGES)
            actions[action] = tuple(perm[i] for i in range(14))
    if len(actions)!=336:
        raise ValueError('Unexpected number of incidence symmetries')
    return sorted(actions.items()), [points[i] for i in range(7)], [normals[i] for i in range(7,14)]


def moved(mask, permutation):
    return sum(1 << permutation[i] for i in range(len(permutation)) if mask >> i & 1)


def floor_library(screens, symmetries):
    table = {}
    for c in screens.values():
        mask,points = c['representative'],c['sample_vertices']
        required = sum(1 << i for i,e in enumerate(ENDS) if mask >> i & 1 and e & points)
        slack = c['gate_cap']-points.bit_count()
        for edges,perm in symmetries:
            key = moved(required,edges)
            if key not in table or table[key][0]<slack:
                table[key] = (slack,mask,perm)
    return sorted([(slack,key,mask,perm) for key,(slack,mask,perm) in table.items()],reverse=True)


def gate_floor(mask, screens, library):
    v = endpoints(mask).bit_count()
    h = len(EDGES)-mask.bit_count()
    j = len(disjoint_matching(mask))
    for slack,required,source,perm in library:
        if required & mask != required:
            continue
        c = screens[source]
        projected = instance(mask,moved(c['sample_vertices'],perm))
        def relabeled(key):
            return {moved(w,perm) for w in c[key]}
        if (not set(projected['signals'])<=relabeled('signals')
                or not relabeled('positive_rows')<=set(projected['positive_rows'])
                or set(projected['negative_rows'])!=relabeled('negative_rows')):
            raise ValueError('Invalid lower-bound certificate')
        return dict(representative=mask,surviving_edges=h,matching=j,lost_endpoints=v,
                    source=source,permutation=list(perm),gate_floor=h+j+v+slack+1)
    return dict(representative=mask,surviving_edges=h,matching=j,lost_endpoints=v,
                source=None,gate_floor=h+j+v-1)


def full_graph_control():
    previous = Path(__file__).resolve().parent.parent/'heawood-125/controls.json'
    cases = json.loads(previous.read_text())['cases']
    codes = next(c['codes'] for c in cases if c['losses']==0)
    assignments = 1 << 14
    columns = [sum(1 << r for r in range(assignments) if r >> v & 1) for v in range(14)]
    target = 0
    for u,v in EDGES:
        target |= columns[u] & columns[v]
    wires = list(columns)
    for code in codes:
        u,v = code%64,(code//64)%64
        if not 0<=code<8192 or max(u,v)>=len(wires):
            raise ValueError('Invalid 27-gate control')
        wires.append(wires[u] & wires[v] if code<4096 else wires[u] | wires[v])
    if len(codes)!=27 or wires[-1]!=target:
        raise ValueError('Full graph upper bound fails')
    return dict(gates=len(codes),assignments=assignments)


def inventory():
    results = json.loads((HERE/'results.json').read_text())
    screens = {c['representative']:c for c in json.loads((HERE/'screens.json').read_text())}
    symmetries,points,normals = fano_actions()
    actions = [edges for edges,_ in symmetries]
    library = floor_library(screens,symmetries)
    out = []
    for layer in [*results['layers'],*results['higher_layers']]:
        seen = set()
        pending = set()
        if 'open_representatives' in layer:
            unclassified = {c['representative'] for c in layer['open_representatives']}
            cases = [*layer['certificates'],*layer['open_representatives']]
        else:
            unclassified = set()
            cases = [dict(representative=r['representative'],size=screens[r['representative']]['orbit_size'])
                     for r in layer['exhaustions']]
        for case in cases:
            m = case['representative']
            ids = [i for i in range(21) if m >> i & 1]
            orbit = {sum(1 << p[i] for i in ids) for p in actions}
            if min(orbit)!=m or len(orbit)!=case['size'] or orbit & seen:
                raise ValueError('Invalid or overlapping orbit')
            seen.update(orbit)
            if m in unclassified:
                pending.update(orbit)
        digest = sha256(b''.join(m.to_bytes(3,'little') for m in sorted(seen))).hexdigest()
        if len(seen)!=layer['candidates'] or digest!=layer['sorted_masks_sha256']:
            raise ValueError('The independent orbit expansion differs from the enumerated masks')
        if len(pending)!=layer.get('remaining',0):
            raise ValueError('Incorrect open-mask count')
        floors = [gate_floor(m,screens,library) for m in sorted(unclassified)]
        if any(q['gate_floor']>26 for q in floors):
            raise ValueError('An open class fails its gate budget')
        floor = min([27,*[q['gate_floor'] for q in floors]])
        out.append(dict(losses=layer['losses'],remaining=len(pending),remaining_orbits=len(unclassified),
                        gate_floor=floor,open_class_bounds=floors,remaining_masks=sorted(pending)))
    return dict(point_coordinates=points,line_normals=normals,automorphisms=len(actions),
                minimum_gate_lower_bound=min([27,*[q['gate_floor'] for q in out]]),
                full_graph_upper_control=full_graph_control(),
                remaining_masks=sum(q['remaining'] for q in out),
                remaining_orbits=sum(q['remaining_orbits'] for q in out),layers=out)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args = p.parse_args()
    result = inventory()
    if args.output:
        args.output.write_text(json.dumps(result,indent=1)+'\n')
    elif result!=json.loads((HERE/'frontier.json').read_text()):
        raise ValueError('The published frontier differs')
    print(f"Reconstructed every candidate orbit. {result['remaining_masks']} edge masks remain in {result['remaining_orbits']} classes.")


if __name__=='__main__':
    main()
