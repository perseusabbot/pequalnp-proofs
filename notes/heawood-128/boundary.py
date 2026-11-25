"""Enumerate the eleven-loss boundary and solve its seven separate gate-budget tests."""
from itertools import combinations
import json
from math import comb
from pathlib import Path
import sys

from theta_check import PRIOR, check_control, exhaust
sys.path.insert(0,str(PRIOR))
from census import cover_table, graph, orbits
from cycle_census import cycle_catalog
from ten_census import patches


def matching_numbers(ends):
    # Enumerate every vertex-disjoint set of edges, then take the maximum
    # matching size over the subsets of each edge mask.
    size=1<<len(ends)
    table=bytearray(size)
    def extend(i,used,mask,count):
        table[mask]=count
        for j in range(i,len(ends)):
            if not used & ends[j]:
                extend(j+1,used|ends[j],mask|(1<<j),count+1)
    extend(0,0,0,0)
    for i in range(len(ends)):
        block=1<<i
        for base in range(block,size,2*block):
            for j in range(base,base+block):
                table[j]=max(table[j],table[j-block])
    return table


def local_instance(edges,mask,products):
    missing=[e for i,e in enumerate(edges) if mask>>i&1]
    surviving=[e for i,e in enumerate(edges) if not mask>>i&1]
    vertices=sorted({v for e in missing for v in e})
    index={u:i for i,u in enumerate(vertices)}
    def word(vs):
        return sum(1<<index[x] for x in vs)
    positive=sorted(word(e) for e in missing)
    internal=[word(e) for e in edges if all(x in index for x in e)]
    def unsafe(row):
        return any((row&e)==e for e in internal)
    negative=[row for row in range(1<<len(index)) if not unsafe(row) and
              all(unsafe(row|(1<<v)) for v in range(len(index)) if not row>>v&1)]
    signals={1<<i for i in range(len(index))}
    for c in range(14):
        near=[b if a==c else a for a,b in surviving if c in (a,b) and (b if a==c else a) in index]
        for size in range(1,len(near)+1):
            signals.update(word(group) for group in combinations(near,size))
    signals=sorted(signals)
    cap=26-len(surviving)-products
    supports,summary=exhaust(signals,positive,negative,(cap,))
    assert not summary[0]['possible']
    # Check a positive control separately on every assignment, including rows
    # outside the boundary sample. It computes the OR of all missing edges.
    ops=[['AND',signals.index(1<<index[u]),signals.index(1<<index[v])] for u,v in missing]
    out=len(signals)
    for i in range(1,len(missing)):
        ops.append(['OR',out,len(signals)+i])
        out=len(signals)+len(ops)-1
    rows=check_control(dict(vertex_order=vertices,control_gates=ops,control_output_port=out),signals,positive)
    return dict(gate_cap=cap,retained_product_lower_bound=products,vertex_order=vertices,
                surviving_edges_inside=sum(e not in positive for e in internal),
                regular_signals=signals,positive_rows=positive,maximal_negative_rows=negative,
                separating_input_sets=len(supports),search=summary[0],control_gates=len(ops),
                control_assignments=rows)


def main():
    edges=graph(PRIOR/'src/HeawoodStages.lean')
    full=(1<<len(edges))-1
    ends=[(1<<u)|(1<<v) for u,v in edges]
    cover,induced=cover_table(edges)
    matching=matching_numbers(ends)
    cycles=cycle_catalog(edges,induced)
    graph_patches=patches(edges,induced,cycles)
    six=[m for claw,_,_,m in graph_patches if not claw]
    weak=[m for claw,_,_,m in graph_patches if claw]+[m for d,m in cycles.items() if d.bit_count()==8]
    candidates=[]
    for lost in combinations(range(21),11):
        m=sum(1<<i for i in lost)
        vertices=branching=0
        for i in lost:
            branching|=vertices&ends[i]
            vertices|=ends[i]
        keep=full^m
        jobs=matching[keep]
        assert jobs==cover[keep]
        base=keep.bit_count()+vertices.bit_count()+jobs-1
        if base>26:
            continue
        bonus=(3 if any(q&m==q for q in six) else 2 if any(q&m==q for q in weak)
               else int(bool(induced[branching]&m)))
        if base+bonus<=26:
            candidates.append(m)
    group=orbits(edges,candidates)
    models=[]
    for orbit in group['orbits']:
        mask=orbit['representative']
        models.append(dict(**orbit,**local_instance(edges,mask,matching[full^mask])))
    assert len(candidates)==1176 and len(models)==7
    assert group['automorphisms']==336 and sum(row['size'] for row in models)==len(candidates)
    print(json.dumps(dict(checked_masks=comb(21,11),matching_checked_on_every_complement=True,
                          prior_candidates=len(candidates),automorphisms=group['automorphisms'],
                          candidates=sorted(candidates),orbits=models,remaining=0),indent=2))


if __name__=='__main__':
    main()
