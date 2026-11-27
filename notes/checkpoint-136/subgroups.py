"""Classify small 2-subgroups and construct their exact rectangle-cover quotients."""
import argparse
from collections import Counter
import json
from pathlib import Path

from plane import BOARD, HERE, IDENTITY, ROWS, bits, group, inverse, require, table
from geometry import ACTIONS, maximal_rectangles, union
from two_groups import ascending, generators_of, index_two, partitions
from search import encode


def sylow(ambient):
    axis_gens=[bytes(g['rows']+[21+i for i in g['columns']]) for g in ACTIONS['two_group_generators']]
    def closure(generators):
        steps=list(map(table,generators))
        elements=[IDENTITY]; seen={IDENTITY}
        for p in elements:
            for step in steps:
                h=p.translate(step)
                if h not in seen:
                    seen.add(h)
                    elements.append(h)
        return elements
    axis=set(closure(axis_gens))
    require(len(axis)==128,'Unexpected axis-preserving 2-group')
    t0=list(map(table,axis_gens))
    def extends(g):
        if g[0]<21 or g.translate(table(g))!=IDENTITY:
            return False
        t=table(g)
        return all(g.translate(s).translate(t) in axis for s in t0)
    dual=next(g for g in ambient if extends(g))
    members=closure(axis_gens+[dual])
    require(len(members)==256 and set(members)<=set(ambient),'Invalid Sylow group')
    index={g:i for i,g in enumerate(members)}
    product=[[index[p.translate(table(q))] for q in members] for p in members]
    return members,product,dual


def conjugacy(members,product,ambient,order):
    subs={s for s in ascending(product,order) if len(s)==order}
    independent={tuple(range(256))}
    size=256
    while size>order:
        independent={k for s in independent for k in index_two(s,product)}
        size//=2
    require(subs==independent,'Ascending and descending subgroup lists differ')
    inv=[r.index(0) for r in product]
    small={}
    while subs:
        s=min(subs)
        orb={tuple(sorted(product[product[g][v]][inv[g]] for v in s)) for g in range(256)}
        require(orb<=subs,'Overlapping Sylow conjugacy classes')
        subs-=orb
        small[tuple(sorted(members[i] for i in s))]=(len(orb),s)
    available={g for s in small for g in s}
    tables=[(g,inverse(g),table(g)) for g in ambient]
    remaining=set(small); result=[]
    while remaining:
        s=min(remaining,key=lambda x:small[x][1])
        generators=[table(g) for g in s if g!=IDENTITY]
        seen=set();normalizer=[]
        for g,inv_g,t in tables:
            first=inv_g.translate(generators[0]).translate(t)
            if first not in available:
                continue
            other=tuple(sorted([IDENTITY,first,*[inv_g.translate(h).translate(t) for h in generators[1:]]]))
            if other==s:
                normalizer.append(g)
            if other in small:
                seen.add(other)
        require(s in seen and seen<=remaining,'Ambient conjugacy classes overlap')
        remaining-=seen
        result.append(dict(subgroup=list(small[s][1]),normalizer=len(normalizer),normalizer_maps=normalizer,
                           sylow_conjugacy_classes=len(seen),in_sylow=sum(small[z][0] for z in seen),
                           full_conjugates=len(ambient)//len(normalizer),
                           exchanges_axes=any(g[0]>=21 for g in s)))
    return result


def perm_mask(g):
    # Five full bytes and the final two labels span the 42-bit rectangle encoding.
    lookup=[]
    for start in range(0,42,8):
        t=[0]
        for j in range(start,min(start+8,42)):
            t += [v|(1<<g[j]) for v in t]
        lookup.append(t)
    def move(w):
        return (lookup[0][w&255]|lookup[1][w>>8&255]|lookup[2][w>>16&255]
                |lookup[3][w>>24&255]|lookup[4][w>>32&255]|lookup[5][w>>40])
    return move


def fixed_boxes(g):
    # If g exchanges the axes and fixes a rectangle, its row set A determines
    # all its columns g(A). Pairwise compatibility is exactly the clique condition.
    c=[x-21 for x in g[:21]]
    allowed=sum(1<<i for i,j in enumerate(c) if ROWS[i]>>j&1)
    neighbors=[sum(1<<j for j in bits(allowed) if i<j and ROWS[i]>>c[j]&1 and ROWS[j]>>c[i]&1)
               for i in range(21)]
    move=perm_mask(g)
    def visit(a,b,left):
        for i in bits(left):
            r=a|1<<i; s=b|1<<c[i]
            box=encode((r,s))
            if move(box)==box:
                yield box
            yield from visit(r,s,left&neighbors[i])
    return visit(0,0,allowed)


def quotient(s, generators, maxboxes):
    boxes=set(maxboxes)
    for g in s:
        if g[0]>=21:
            boxes.update(fixed_boxes(g))
    cells=[(i,j) for i,w in enumerate(ROWS) for j in bits(w)]
    ix={encode((1<<i,1<<j)):k for k,(i,j) in enumerate(cells)}
    moves=[perm_mask(g) for g in generators]
    cell_perms=[[ix[f(w)] for w in ix] for f in moves]
    orbits=list(partitions(cell_perms,len(cells)))
    cell_index={cells[v]:i for i,orb in enumerate(orbits) for v in orb}
    count=len(boxes); pool={}
    symmetries=[perm_mask(g) for g in s]
    while boxes:
        w=next(iter(boxes))
        orbit={f(w) for f in symmetries}
        require(orbit<=boxes,'Candidate rectangle orbits overlap or are incomplete')
        boxes.difference_update(orbit)
        a=w&BOARD; b=w>>21
        mask=union(1<<cell_index[i,j] for i in bits(a) for j in bits(b))
        cost=len(orbit)
        require(cost in (1,2,4,8,16) and len(s)%cost==0,'Invalid rectangle orbit')
        pool[mask]=min(cost,pool.get(mask,cost))
    return orbits,count,pool


def instances(out,order,ambient,members,product,dual):
    out.mkdir(parents=True,exist_ok=True)
    classes=conjugacy(members,product,ambient,order)
    maxboxes={encode(box) for box in maximal_rectangles()}
    for i,r in enumerate(classes):
        subgroup=r['subgroup']
        gen=[members[j] for j in generators_of(subgroup,product)]
        orbits,box_count,pool=quotient([members[j] for j in subgroup],gen,maxboxes)
        cells=[(p,l) for p,v in enumerate(ROWS) for l in bits(v)]
        places={encode((1<<cells[index][0],1<<cells[index][1])):j for j,orb in enumerate(orbits) for index in orb}
        leaders=[encode((1<<cells[orb[0]][0],1<<cells[orb[0]][1])) for orb in orbits]
        sym=set()
        for g in r.pop('normalizer_maps'):
            move=perm_mask(g)
            action=tuple(places[move(w)] for w in leaders)
            require(sorted(action)==list(range(len(orbits))),'Induced map is not a permutation')
            sym.add(action)
        with (out/f'class-{i}.sym').open('w') as f:
            print(len(sym),file=f)
            for perm in sorted(sym):print(*perm,file=f)
        r.update(id=i,cell_orbits=len(orbits),quotient_symmetries=len(sym),candidate_rectangles=box_count,distinct_costs=dict(sorted(Counter(pool.values()).items())))
        with (out/f'class-{i}.in').open('w') as f:
            print(len(orbits),15,sum(c<=15 for c in pool.values()),file=f)
            for m,c in sorted(pool.items()):
                if c<=15:print(c,m%(1<<64),m>>64,file=f)
    report=dict(order=order,side_swapping_generator=list(dual),classes=classes,
                subgroups_in_sylow=sum(r['in_sylow'] for r in classes),subgroups_in_group=sum(r['full_conjugates'] for r in classes))
    (out/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory',type=Path,help='Destination for quotient instances and class inventory')
    ap.add_argument('--order',type=int,choices=(4,8,16),default=8)
    args=ap.parse_args()
    ambient=group()
    report=instances(args.directory,args.order,ambient,*sylow(ambient))
    print(len(report['classes']),'conjugacy classes,',report['subgroups_in_group'],'subgroups')


if __name__=='__main__':
    main()
