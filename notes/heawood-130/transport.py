"""Transport checked finite obstructions and reconstruct each previous open orbit."""
from functools import cache
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'heawood-129'
sys.path.insert(0, str(PARENT))
from instances import EDGES, ENDS, disjoint_matching, endpoints, instance
from frontier import fano_actions, full_graph_control, moved

DIRECT = ((114175, 10151), (114686, 13727), (126463, 10151), (126719, 13727))
EXTRAS = sorted({sum(1 << u for u in subset)
                 for v in range(14)
                 for neighbors in [[y if x == v else x for x, y in EDGES if v in (x, y)]]
                 for width in (2, 3) for subset in combinations(neighbors, width)})
EXTRA_INDEX = {s: i for i, s in enumerate(EXTRAS)}
EDGE_INDEX = {e: i for i, e in enumerate(ENDS)}


def read(path):
    return json.loads(path.read_text())


def source_screens():
    return read(PARENT / 'screens.json') + [instance(m, t) for m, t in DIRECT]


def extra_code(signals):
    return sum(1 << EXTRA_INDEX[w] for w in signals if w.bit_count() > 1)


@cache
def library():
    symmetries = fano_actions()[0]
    entries = {}
    for c in source_screens():
        for edges, perm in symmetries:
            t = moved(c['sample_vertices'], perm)
            p = sum(1 << edges[EDGE_INDEX[r]] for r in c['positive_rows'])
            x = extra_code(moved(s, perm) for s in c['signals'])
            key = t, p, x
            entry = c['gate_cap'] + 1, c['representative'], perm
            if key not in entries or entries[key][0] < entry[0]:
                entries[key] = entry
    return entries


@cache
def restricted_extras(mask, t):
    neighborhoods = [0] * 14
    for i, (a, b) in enumerate(EDGES):
        if not mask >> i & 1:
            neighborhoods[a] |= t & (1 << b)
            neighborhoods[b] |= t & (1 << a)
    return sum(1 << i for i, s in enumerate(EXTRAS) if any(s & n == s for n in neighborhoods))


def inventory(global_floor, local_floors=()):
    parents = read(PARENT / 'frontier.json')
    sources = {c['representative']: c for c in source_screens()}
    order = sorted(library().items(), key=lambda v: (-(v[1][0]-v[0][0].bit_count()), v[0]))
    symmetries = [edges for edges, _ in fano_actions()[0]]
    if len(set(symmetries)) != 336:
        raise ValueError('Incomplete symmetry group')
    floors = dict(local_floors)
    layers = []
    for old in (s for s in parents['layers'] if s['remaining']):
        known = set(old['remaining_masks'])
        seen, remaining, records = set(), set(), []
        for row in old['open_class_bounds']:
            m = row['representative']
            orbit = {moved(m, action) for action in symmetries}
            if m != min(orbit) or seen & orbit or not orbit <= known:
                raise ValueError('Invalid symmetry assignment')
            seen.update(orbit)
            v = endpoints(m)
            paid = 21-m.bit_count()+len(disjoint_matching(m))
            for (t, p, x), (local, source, perm) in order:
                if t & ~v or p & ~m or restricted_extras(m, t) & ~x:
                    continue
                c = sources[source]
                sample = instance(m, t)
                def mapped(field):
                    return {moved(w, perm) for w in c[field]}
                if (not set(sample['signals']) <= mapped('signals')
                        or not mapped('positive_rows') <= set(sample['positive_rows'])
                        or set(sample['negative_rows']) != mapped('negative_rows')):
                    raise ValueError('Incompatible transport')
                bound = paid + (v & ~t).bit_count() + local
                break
            else:
                raise ValueError('No matching source')
            floor = max(global_floor, bound, row['gate_floor'], floors.get(m, 0))
            if floor <= 26:
                remaining.update(orbit)
            records.append(dict(representative=m, size=len(orbit), source=source,
                                permutation=list(perm), sample_vertices=t, local_floor=local,
                                surviving_edges=21-m.bit_count(), matching=disjoint_matching(m),
                                lost_endpoints=v.bit_count(), projected_gate_floor=bound,
                                prior_floor=row['gate_floor'], gate_floor=floor))
        if seen != known:
            raise ValueError('Parent orbit cover differs')
        data = sorted(remaining)
        digest = sha256(b''.join(m.to_bytes(3, 'little') for m in data)).hexdigest()
        layers.append(dict(losses=old['losses'], previous_orbits=len(records), previous_masks=len(seen),
                           gate_floor=min([27] + [r['gate_floor'] for r in records]),
                           remaining_orbits=sum(r['gate_floor'] <= 26 for r in records),
                           remaining=len(data), remaining_masks=data, remaining_sha256=digest,
                           class_bounds=records))
    return dict(automorphisms=len(symmetries), prior_remaining_masks=sum(r['previous_masks'] for r in layers),
                prior_remaining_orbits=sum(r['previous_orbits'] for r in layers),
                remaining_masks=sum(r['remaining'] for r in layers),
                remaining_orbits=sum(r['remaining_orbits'] for r in layers),
                global_gate_floor=global_floor, upper_control=full_graph_control(), layers=layers)
