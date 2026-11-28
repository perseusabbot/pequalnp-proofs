"""Try every way of retaining five rectangles from the published size-15 cover at budget 14."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from itertools import combinations
from math import comb
from pathlib import Path
import json
import subprocess
from tempfile import TemporaryDirectory

from replay import program
from input_data import HERE, ROWS, geometry, group, require
from rectangles import bits, covered_rows, perm_mask


def retained_orbits(boxes):
    keys=[a | b<<21 for a,b in boxes];index={w:i for i,w in enumerate(keys)}
    shapes=[tuple(sorted((a.bit_count(),b.bit_count()))) for a,b in boxes]
    first=keys[0];indices=list(bits(first));possible={w for w,s in zip(keys,shapes) if s==shapes[0]}
    actions=[]
    for g in group():
        if sum(1<<g[j] for j in indices) not in possible:continue
        move=perm_mask(g);images=[move(w) for w in keys]
        if all(w in index for w in images):actions.append([index[w] for w in images])
    require(actions and all(len(set(v))==15 for v in actions),'Invalid stabilizer')
    pool={sum(1<<i for i in t) for t in combinations(range(15),5)};orbits=[]
    while pool:
        m=min(pool);ids=list(bits(m));orbit={sum(1<<p[i] for i in ids) for p in actions}
        require(m in orbit and orbit<=pool,'Retained-set orbits intersect')
        pool-=orbit;orbits.append((m,len(orbit)))
    require(sum(n for _,n in orbits)==comb(15,5),'Missing five-subset')
    return actions,orbits


def run(folder,jobs):
    boxes=json.loads((HERE.parent/'checkpoint-134/board.json').read_text())['published_fifteen']
    require(covered_rows(boxes)==list(ROWS),'The published cover differs')
    actions,orbits=retained_orbits(boxes);board=folder/'board';board.write_text(geometry())
    solver=program('controls',folder)
    def part(offset):
        chunk=orbits[offset::jobs];input_rows=[]
        for m,_ in chunk:
            used=covered_rows([boxes[j] for j in bits(m)])
            input_rows.append(' '.join(map(str,[9,*[r&~v for r,v in zip(ROWS,used)]])))
        raw=subprocess.check_output([solver,board],input='\n'.join(input_rows)+'\n',text=True).splitlines()
        require(len(raw)==len(chunk),'A retained set was omitted')
        answers=[]
        for (m,weight),s in zip(chunk,raw):
            kind,states,*rest=s.split();witness=None
            if kind=='COVER':
                sides=list(map(int,rest));witness=[boxes[j] for j in bits(m)]+[list(t) for t in zip(sides[::2],sides[1::2]) if all(t)]
                require(len(witness)<=14 and covered_rows(witness)==list(ROWS),'Invalid 14-rectangle witness')
            else:require(kind=='EXCLUDED' and not rest,'Invalid coloring conclusion')
            answers.append([m,weight,int(states),witness])
        return answers
    with ThreadPoolExecutor(max_workers=jobs) as pool:groups=list(pool.map(part,range(jobs)))
    rows=sorted(v for chunk in groups for v in chunk)
    return dict(published_rectangles=15,retained=5,budget=14,stabilizer_order=len(actions),representatives=len(rows),
                physical_five_subsets=sum(v[1] for v in rows),states=sum(v[2] for v in rows),
                all_decisions_sha256=sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),
                covers=[v[3] for v in rows if v[3] is not None])


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--jobs',type=int,default=1);ap.add_argument('--output',type=Path)
    args=ap.parse_args();require(args.jobs>0,'Invalid worker count')
    with TemporaryDirectory() as tmp:r=run(Path(tmp),args.jobs)
    if args.output:args.output.write_text(json.dumps(r,indent=2)+'\n')
    else:require(r==json.loads((HERE/'neighbors.json').read_bytes()),'Published neighborhood differs')
    print(r['representatives'],'retained sets checked,',len(r['covers']),'covers found')
