"""Find the possible sizes of orbits under a concrete group of 128 axis-preserving maps."""
import argparse
from array import array
import json
import os
from pathlib import Path
import subprocess
import tempfile

from geometry import ACTIONS, HERE, IDENTITY, ROWS, bits, group, maximal_rectangles, permute, require, union


def generated(perms, ambient):
    generators=[bytes(g['rows']+[21+j for j in g['columns']]) for g in perms]
    require(all(g in ambient for g in generators),'Generator outside the board group')
    tables=[bytes.maketrans(IDENTITY,g) for g in generators]
    elems=[IDENTITY]; index={IDENTITY:0}; paths=[None]
    for i,g in enumerate(elems):
        for j,t in enumerate(tables):
            dst=g.translate(t)
            if dst not in index:
                paths.append((i,j))
                index[dst]=len(elems)
                elems.append(dst)
    require(len(elems)==128 and all(g[0]<21 for g in elems),'Unexpected axis-preserving group')
    product=[[index[a.translate(bytes.maketrans(IDENTITY,b))] for b in elems] for a in elems]
    return generators,paths,product


def generators_of(subgroup, product):
    seen={0}; generators=[]
    for g in subgroup:
        if g in seen:
            continue
        generators.append(g)
        queue=list(seen)
        for h in queue:
            for k in generators:
                other=product[h][k]
                if other not in seen:
                    seen.add(other)
                    queue.append(other)
    require(seen==set(subgroup),'Set of elements is not a subgroup')
    return generators


def index_two(subgroup, product):
    # Express every element as a word in generators and record the word's
    # parity vector. Every relator must have even dot product with a homomorphism to C2.
    generators=generators_of(subgroup,product)
    labels={0:0}; queue=[0]; relations=set()
    for h in queue:
        for j,k in enumerate(generators):
            destination=product[h][k]
            value=labels[h]^(1<<j)
            if destination in labels:
                relations.add(labels[destination]^value)
            else:
                queue.append(destination)
                labels[destination]=value
    require(len(labels)==len(subgroup),'Incomplete parity traversal')
    for mask in range(1,1<<len(generators)):
        if all((mask&r).bit_count()%2==0 for r in relations):
            kernel=tuple(sorted(g for g,v in labels.items() if (mask&v).bit_count()%2==0))
            require(2*len(kernel)==len(subgroup),'Wrong kernel size')
            yield kernel


def ascending(product, maximum):
    # Independently generate subgroups by adjoining a single element. Every
    # subgroup of the requested size has a chain of generating subsets of at most that size.
    start=(0,)
    known={start}; queue=[start]
    for s in queue:
        if len(s)==maximum:
            continue
        gen=generators_of(s,product)
        remaining=set(range(len(product)))-set(s)
        while remaining:
            g=min(remaining)
            # Every element of the coset Sg generates the same extension with S.
            remaining-={product[h][g] for h in s}
            gs=[*gen,g]
            got=set(s); work=list(s)
            for u in work:
                for v in gs:
                    y=product[u][v]
                    if y not in got:
                        got.add(y);work.append(y)
                if len(got)>maximum:
                    break
            if len(got)<=maximum:
                key=tuple(sorted(got))
                if key not in known:
                    known.add(key);queue.append(key)
    return known


def induced(generator_actions,paths,n):
    perms=[array('H',range(n))]
    for parent,g in paths[1:]:
        perms.append(array('H',(generator_actions[g][i] for i in perms[parent])))
    return perms


def partitions(permutations, size):
    seen=bytearray(size)
    for i in range(size):
        if seen[i]:
            continue
        orbit=[i];seen[i]=1
        for v in orbit:
            for perm in permutations:
                t=perm[v]
                if not seen[t]:
                    seen[t]=1;orbit.append(t)
        yield orbit


def board_actions(generators,paths):
    cells=[(i,j) for i,r in enumerate(ROWS) for j in bits(r)]
    boxes=sorted(maximal_rectangles())
    idx={c:i for i,c in enumerate(cells)}
    box_idx={b:i for i,b in enumerate(boxes)}
    cell_actions=[];box_actions=[]
    for g in generators:
        p=g[:21];q=[t-21 for t in g[21:]]
        cell_actions.append([idx[p[i],q[j]] for i,j in cells])
        box_actions.append([box_idx[permute(a,p),permute(b,q)] for a,b in boxes])
    occupied=[[idx[i,j] for i in bits(a) for j in bits(b)] for a,b in boxes]
    return induced(cell_actions,paths,len(cells)),induced(box_actions,paths,len(boxes)),occupied


def quotient_pool(generators, actions, cap):
    cell_actions,box_actions,occupied=actions
    orbits=list(partitions([cell_actions[i] for i in generators],len(cell_actions[0])))
    cell_index={p:i for i,orb in enumerate(orbits) for p in orb}
    pool={}
    for orbit in partitions([box_actions[i] for i in generators],len(occupied)):
        cost=len(orbit)
        if cost<=cap:
            mask=union(1<<cell_index[i] for i in occupied[orbit[0]])
            pool[mask]=min(pool.get(mask,cost),cost)
    return len(orbits),pool


def weighted(binary,n,pool,cap):
    choices=[(m,c) for m,c in pool.items() if c<=cap]
    data=[f'{n} {cap} {len(choices)}',*(f'{c} {m%2**64} {m>>64}' for m,c in choices)]
    word,nodes=subprocess.check_output([binary],input='\n'.join(data)+'\n',text=True).split()
    require(word in ('COVER','EXCLUDED'),'Unrecognized budget result')
    return word=='COVER',int(nodes)


def run(minimum,raw):
    generators,paths,product=generated(ACTIONS['two_group_generators'],group())
    actions=board_actions(generators,paths)
    subgroups={tuple(range(128))}
    inverse=[row.index(0) for row in product]
    independently=ascending(product,minimum)
    out={}
    with tempfile.TemporaryDirectory() as tmp:
        binary=Path(tmp)/'budget'
        subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(HERE/'budget.cpp'),'-o',str(binary)],check=True)
        size=128
        while size>=minimum:
            if size<128:
                subgroups={k for s in subgroups for k in index_two(s,product)}
            if size==minimum:
                require(subgroups=={s for s in independently if len(s)==size},'Subgroup enumerations disagree')
            todo=set(subgroups)
            records=[]
            while todo:
                s=min(todo)
                orbit={tuple(sorted(product[product[g][v]][inverse[g]] for v in s)) for g in range(128)}
                require(orbit<=todo,'Overlapping subgroup classes')
                todo-=orbit
                items=sorted(orbit) if raw else [s]
                answers=[]
                for member in items:
                    n,pool=quotient_pool(generators_of(member,product),actions,15)
                    best=16
                    for cap in (15,14,13):
                        yes,_=weighted(binary,n,pool,cap)
                        if not yes:
                            break
                        best=cap
                    answers.append(best)
                require(len(set(answers))==1,'Conjugates give different answers')
                records.append((len(orbit),answers[0]))
            require(sum(m for m,_ in records)==len(subgroups),'Missing subgroup')
            counts={str(cap):sum(m for m,b in records if b<=cap) for cap in (13,14,15)}
            out[str(size)]=dict(subgroups=len(subgroups),conjugacy_classes=len(records),admitting_cover_at_most=counts)
            size//=2
    return out


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--minimum-order',type=int,choices=(8,16,32,64,128),default=16)
    ap.add_argument('--all-subgroups',action='store_true',help='Test every subgroup individually, including conjugates')
    args=ap.parse_args()
    print(json.dumps(run(args.minimum_order,args.all_subgroups),indent=2))
