"""Test fourteen-rectangle covers with three exceptions, two in area-sixteen maximal boxes."""
import argparse
from collections import Counter
from math import comb
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from replay import HERE, bits, build, case, covered_rows, digest, execute, group, inventory, perm_mask, prefix, require, six_rectangles
from rectangles import BOARD, maximal_rectangles


def unpack(w):
    return w & BOARD,w >> 21


def area(w):
    a,b = unpack(w)
    return a.bit_count()*b.bit_count()


def assemble():
    pairs,_ = inventory()
    exceptional = {a | b<<21 for a,b in maximal_rectangles() if a.bit_count()*b.bit_count()!=36}
    small = {w for w in exceptional if area(w)==16}
    require(len(exceptional)==25067 and len(small)==147,'Incorrect rectangle inventory')
    require(all(area(w)>=24 for w in exceptional-small),'Unexpected intermediate area')
    elements = group()
    roots = [(i,p) for i,p in enumerate(pairs) if p[0] in small and p[1] in small]
    pair_mass = Counter()
    triples,summary = [],[]
    for root in sorted({p[0] for _,p in roots}):
        labels = list(bits(root))
        stabilizer = [g for g in elements if all(root>>g[j]&1 for j in labels)]
        root_count = len(elements)//len(stabilizer)
        for index,(a,b,pair_size) in roots:
            if a!=root:
                continue
            same = list(bits(b))
            maps = [perm_mask(g) for g in stabilizer if all(b>>g[j]&1 for j in same)]
            require(len(maps)*pair_size==len(stabilizer),'Wrong marked-pair stabilizer')
            shape = tuple(sorted(min(x.bit_count() for x in unpack(w)) for w in (a,b)))
            pair_mass[shape] += root_count*pair_size
            left = exceptional-{a,b}
            start,total = len(triples),0
            while left:
                third = min(left)
                orbit = {move(third) for move in maps}
                require(third in orbit and orbit<=left,'Third-rectangle orbits overlap')
                left -= orbit
                total += len(orbit)
                triples.append((a,b,third,len(orbit)))
            require(total==len(exceptional)-2,'Incomplete third-rectangle inventory')
            summary.append(dict(pair_case=index,orbit_pairs=root_count*pair_size,
                                third_cases=len(triples)-start))
    # The earlier pair inventory keeps order for equal shapes, with the star orbit first for mixed shapes.
    require(len(roots)==9 and pair_mass=={(1,1):42*41,(1,4):42*105,(4,4):105*104},'Incomplete pair list')
    physical = comb(147,2)*(25067-147)+comb(147,3)
    return triples,summary,physical


def report(jobs, binary):
    triples,anchors,physical = assemble()
    boxes = six_rectangles()
    inputs = [case(11,0,-1,-1,[],-1,covered_rows([unpack(w) for w in t[:3]])) for t in triples]
    board = prefix(boxes)
    out = execute(binary,board,inputs,jobs)
    counts = []
    for i,(row,t) in enumerate(zip(out,triples)):
        if row[0]=='COVER':
            ids = list(map(int,row[3:]))
            candidate = [unpack(w) for w in t[:3]]+[boxes[k] for k in ids]
            require(len(ids)==len(set(ids))<=11 and covered_rows(candidate)==list(ROWS),'Invalid candidate')
            raise RuntimeError(f'Complete size-{len(candidate)} cover at case {i}: {candidate}')
        require(len(row)==3 and row[0]=='EXCLUDED','Unexpected solver output')
        counts.append([int(row[1]),int(row[2])])
    return dict(physical_unordered_triples=physical,marked_pair_roots=anchors,
                cases=len(triples),all_three_small_cases=sum(area(t[2])==16 for t in triples),
                input_sha256=digest(board+''.join(inputs)),total_states=sum(n for n,p in counts),
                total_root_profiles=sum(p for n,p in counts),decisions=counts)


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs',type=int,default=1)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    require(args.jobs>=1,'At least one worker is required')
    with TemporaryDirectory() as temp:
        result = report(args.jobs,build(HERE/'degree_search.cpp',Path(temp)))
    if args.output:
        import re
        text = re.sub(r'\[\s+(\d+),\s+(\d+)\s+\]',r'[\1, \2]',json.dumps(result,indent=2))
        args.output.write_text(text+'\n')
    else:
        require(result==json.loads((HERE/'triples.json').read_text()),'Triple receipt differs')
    print(result['cases'],'representatives of',result['physical_unordered_triples'],
          'triples excluded in',result['total_states'],'states')
