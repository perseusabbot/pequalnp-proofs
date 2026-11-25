"""Transport the certified local bounds across all Checkpoint 130 survivors."""
from hashlib import sha256
from geometry131 import (ALL, EDGE_INDEX, GROUP, PREVIOUS, disjoint_matching, endpoints, extra_code,
                         full_graph_control, moved, read, require, restricted_extras, sample)


def projections(known):
    entries = {}
    for (m,t), floor in sorted(known.items()):
        local = sample(m,t)
        for edges, perm in GROUP:
            domain = moved(t,perm)
            positives = sum(1 << edges[EDGE_INDEX[r]] for r in local['positive_rows'])
            extras = extra_code(moved(s,perm) for s in local['signals'])
            key = (domain,positives,extras)
            if key not in entries or entries[key][0] < floor:
                entries[key] = (floor,m,t,perm)
    # For a fixed representative, only floor minus domain size changes the total bound.
    return sorted(entries.items(),key=lambda entry: (entry[0][0].bit_count()-entry[1][0],entry[0]))


def inventory(known):
    older = read(PREVIOUS/'frontier.json')
    order = projections(known)
    groups = [edges for edges,_ in GROUP]
    require(len(set(groups)) == 336, 'Incorrect group order')
    layers = []
    for previous in older['layers']:
        old = set(previous['remaining_masks'])
        seen, remaining, records = set(), set(), []
        for item in previous['class_bounds']:
            mask, prior = item['representative'], item['gate_floor']
            if prior > 26:
                continue
            orbit = {moved(mask,perm) for perm in groups}
            require(min(orbit)==mask and not (orbit & seen) and orbit <= old, 'Wrong symmetry class')
            seen.update(orbit)
            vertices = endpoints(mask)
            survivors = 21-mask.bit_count()
            matching = disjoint_matching(mask)
            for (t,p,x),(lower,src,src_t,perm) in order:
                if t & ~vertices or p & ~mask or restricted_extras(mask,t) & ~x:
                    continue
                local, target = sample(src,src_t), sample(mask,t)
                def mapped(key):
                    return {moved(r,perm) for r in local[key]}
                require(set(target['signals']) <= mapped('signals')
                        and mapped('positive_rows') <= set(target['positive_rows'])
                        and mapped('negative_rows') == set(target['negative_rows']), 'Invalid transfer')
                outside = (vertices & ~t).bit_count()
                bound = survivors + len(matching) + outside + lower
                floor = max(bound,prior,known[(ALL,16383)])
                records.append(dict(representative=mask,size=len(orbit),prior_floor=prior,
                                    retained_edges=survivors,matching=matching,outside_vertices=outside,
                                    source=[src,src_t,lower],sample_vertices=t,permutation=list(perm),
                                    projected_gate_floor=bound,gate_floor=floor))
                if floor <= 26:
                    remaining.update(orbit)
                break
            else:
                raise ValueError('No verified source')
        require(seen==old,'Missing prior class')
        masks = sorted(remaining)
        layers.append(dict(losses=previous['losses'],previous_orbits=len(records),previous_masks=len(seen),
                           gate_floor=min([27]+[r['gate_floor'] for r in records]),
                           remaining_orbits=sum(r['gate_floor']<=26 for r in records),
                           remaining=len(masks),remaining_masks=masks,class_bounds=records,
                           remaining_sha256=sha256(b''.join(m.to_bytes(3,'little') for m in masks)).hexdigest()))
    return dict(automorphisms=len(groups),prior_remaining_masks=older['remaining_masks'],
                prior_remaining_orbits=older['remaining_orbits'],remaining_masks=sum(r['remaining'] for r in layers),
                remaining_orbits=sum(r['remaining_orbits'] for r in layers),global_gate_floor=known[(ALL,16383)],
                upper_control=full_graph_control(),layers=layers)
