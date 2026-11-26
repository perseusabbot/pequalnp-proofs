"""Exhaust the size-15 cases for the two remaining order-three classes."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import partial
from itertools import combinations
import json
from math import comb
import os
from pathlib import Path
import subprocess
import tempfile

from geometry import (ACTIONS, HERE, IDENTITY, NAMES, ROWS, axes, bits, check_cover,
                      group, maximal_rectangles, normalizer, permute, quotient, require, union)
from verify import direct_four

MASK64 = (1 << 64)-1


def encode(box):
    return box[0] | (box[1] << 21)


def perm_table(g):
    return bytes.maketrans(IDENTITY,g)


def powers(h, k):
    value=IDENTITY
    step=perm_table(h)
    for _ in range(k):
        yield value
        value=value.translate(step)


def fixed_triples(fixed, normal):
    n=len(fixed)
    index={encode(box):i for i,(box,_) in enumerate(fixed)}
    perms={tuple(index[permute(w,g)] for w in index) for g in normal}
    seen=bytearray(n**3)
    out=[]
    for a,b,c in combinations(range(n),3):
        if seen[(a*n+b)*n+c]:
            continue
        images={tuple(sorted((g[a],g[b],g[c]))) for g in perms}
        for x,y,z in images:
            key=(x*n+y)*n+z
            require(not seen[key],'Overlapping fixed triple classes')
            seen[key]=1
        out.append((fixed[a][1] | fixed[b][1] | fixed[c][1],len(images)))
    require(sum(k for _,k in out)==comb(n,3),'Incomplete fixed triple partition')
    return out


def leaders(moving, normal, h, board, slots):
    half=[i for i,(_,w) in enumerate(moving) if slots*(w & board).bit_count()>=board.bit_count()]
    todo=set(half)
    rotations=list(powers(h,3))
    lookup={permute(encode(box),u):i for i,(box,_) in enumerate(moving) for u in rotations}
    require(len(lookup)==3*len(moving),'Incomplete moving orbit inventory')
    reps=[]
    while todo:
        i=min(todo)
        word=encode(moving[i][0])
        images={lookup[permute(word,g)] for g in normal}
        require(images<=todo,'Leader area or orbit overlaps')
        todo-=images
        reps.append((i,len(images)))
    require(sum(k for _,k in reps)==len(half),'Incomplete moving orbit partition')
    return reps


def fewer_movers(boundary, movers):
    # Choose a largest member first. The second has at least half the
    # remaining area if either of the remaining two can finish the cover.
    words=sorted(set(w & boundary for w in movers),key=lambda w:(-w.bit_count(),w))
    require(boundary and words and boundary not in words, 'A single moving orbit reaches the boundary')
    post={j:sum(1<<i for i,w in enumerate(words) if w>>j&1) for j in bits(boundary)}
    full=(1<<len(words))-1
    for i,a in enumerate(words):
        if 3*a.bit_count()<boundary.bit_count():
            break
        left=boundary & ~a
        for b in words[i+1:]:
            if 2*b.bit_count()<left.bit_count():
                break
            if 2*(b & left).bit_count()<left.bit_count():
                continue
            possibilities=full
            for j in bits(left & ~b):
                possibilities &= post[j]
                if not possibilities:
                    break
            require(not possibilities,'Three moving orbits cover the boundary')


def halves(word):
    return f'{word & MASK64} {word >> 64}'


def four(binary, n, movers, residuals):
    masks=[w for w,_ in residuals]
    lines=[f'{n} {len(movers)} {len(masks)}', *(halves(w) for w in movers), *(halves(w) for w in masks)]
    out=subprocess.check_output([binary],input='\n'.join(lines)+'\n',text=True).split()
    require(len(out)==2 and int(out[0])==len(masks),'Incomplete four-orbit run')
    return {'classes':len(masks),'choices':sum(k for _,k in residuals),'final_queries':int(out[1])}


def boundary_first(binary,n,fixes,movers,boundary,reps):
    rim=list(bits(boundary))
    lines=[f'{n} {len(rim)} {len(fixes)} {len(movers)} {len(reps)}', *(halves(w) for w in fixes)]
    for w in movers:
        compressed=sum(1<<j for j,i in enumerate(rim) if w>>i&1)
        lines.append(f'{halves(w)} {compressed}')
    lines.extend(str(i) for i,_ in reps)
    out=subprocess.check_output([binary],input='\n'.join(lines)+'\n',text=True).split()
    require(len(out)==2 and int(out[0])==len(reps),'Incomplete boundary-first run')
    return {'leader_classes':len(reps),'boundary_completions_tested':int(out[1])}


def stabilizer(family,elements):
    words={encode(b) for b in family}
    seed=min(words)
    return [g for g in elements if permute(seed,g) in words and {permute(b,g) for b in words}==words]


def analyze(name, maximal, elements, binaries, independent, jobs):
    p,q,k=axes(name)
    h=bytes(p+[21+i for i in q])
    normal=normalizer(elements,p,q)
    cells,fixed,moving=quotient(maximal,p,q,k)
    n=len(cells)
    board=(1<<n)-1
    F=[w for _,w in fixed]
    M=[w for _,w in moving]
    rim=board & ~union(F)
    fewer_movers(rim,M)
    triples=fixed_triples(fixed,normal)
    first=leaders(moving,normal,h,board,5)
    direct=four(binaries[0],n,M,triples)
    five=four(binaries[0],n,M,[(M[i],size) for i,size in first])
    witness=ACTIONS[name]['witness']
    check_cover(witness,p,q,16)
    stab=stabilizer(witness,elements)
    cycles3=Counter(sum(g[i]==i for i in range(21)) for g in stab
                    if g!=IDENTITY and list(powers(g,4))[-1]==IDENTITY)
    result=dict(order=k,fixed_rows=sum(i==p[i] for i in range(21)),cell_orbits=n,
                fixed_maximal=len(F),moving_maximal_orbits=len(M),boundary_orbits=rim.bit_count(),
                max_single_boundary=max((m&rim).bit_count() for m in M),boundary_triples=0,
                normalizer=len(normal),conjugate_subgroups=len(elements)//len(normal),
                four_moving_three_fixed=direct,five_moving=five,invariant_minimum=16,
                upper_stabilizer=len(stab),upper_images=len(elements)//len(stab),
                upper_order_three_by_fixed_rows=dict(sorted(cycles3.items())))
    if independent:
        anchors=leaders(moving,normal,h,rim,4)
        second=boundary_first(binaries[1],n,F,M,rim,anchors)
        fn=partial(direct_four,movers=M)
        needs=[board & ~M[i] for i,_ in first]
        if jobs==1:
            probes=list(map(fn,needs))
        else:
            with ProcessPoolExecutor(max_workers=jobs) as pool:
                probes=list(pool.map(fn,needs,chunksize=2))
        result['independent']={'four_moving_three_fixed':second,
                               'five_moving':{'leader_classes':len(probes),'final_queries':sum(probes)}}
    return result


def consequences(elements,classes):
    representative=[((i+7)%21) for i in range(21)]
    singer=len(elements)//len(normalizer(elements,representative,representative))
    classes3=Counter()
    excluded={}
    for prime in (3,5,7):
        order=[]
        for g in elements:
            if g==IDENTITY:
                continue
            t=perm_table(g)
            power=g
            for _ in range(prime-1):
                power=power.translate(t)
            if power==IDENTITY:
                order.append(g)
        if prime==3:
            for g in order:
                a=sum(g[i]==i for i in range(21))
                require(g[0]<21 and a==sum(g[21+i]==21+i for i in range(21)), 'Bad order-three row type')
                classes3[a]+=1
            expected={0:2*singer,**{v['fixed_rows']:2*v['conjugate_subgroups'] for v in classes.values()}}
            require(classes3==expected,'Conjugate subgroups do not exhaust order three')
        else:
            if prime==5:
                p,q,_=axes('five')
            else:
                p=q=[(i+3)%21 for i in range(21)]
            h=bytes(p+[21+i for i in q])
            hs=set(powers(h,prime))-{IDENTITY}
            require(len(hs)==prime-1 and h in order,'Unexpected subgroup')
            size=sum(any(h.translate(perm_table(g))==g.translate(perm_table(u)) for u in hs) for g in elements)
            require(len(order)*size==(prime-1)*len(elements),'Missing prime-order conjugacy class')
        excluded[str(prime)]=len(order)
    require(len(elements)==2**8*3**3*5*7,'Group factorization differs')
    # At size 15 a nontrivial row stabilizer in a 3-Sylow subgroup
    # would contain a forbidden order-three element with a fixed row.
    return dict(group_order=len(elements),elements_of_prime_order=excluded,
                order_three_by_fixed_rows=dict(sorted(classes3.items())),
                subgroups_of_order_three=sum(classes3.values())//2,
                orbit_divisor_at_most_14=3**3*5*7,orbit_divisor_at_most_15=3**2*5*7)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--independent',action='store_true',help='Repeat using moving-boundary-first and Python postings')
    ap.add_argument('--jobs',type=int,default=1)
    args=ap.parse_args()
    require(args.jobs>=1,'At least one worker is required')
    elements=group()
    maximal=maximal_rectangles()
    require(len(maximal)==25235,'Maximal rectangle count differs')
    with tempfile.TemporaryDirectory() as tmp:
        binaries=[]
        for name in (['four','boundary'] if args.independent else ['four']):
            file=Path(tmp)/name
            subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(HERE/(name+'.cpp')),'-o',str(file)],check=True)
            binaries.append(file)
        results={name:analyze(name,maximal,elements,binaries,args.independent,args.jobs) for name in NAMES}
    print(json.dumps(dict(classes=results,group=consequences(elements,results)),indent=2))

if __name__=='__main__':
    main()
