"""Replay the finite cover searches, degree families, and positive controls."""
import argparse
from collections import Counter,defaultdict
from concurrent.futures import ThreadPoolExecutor
from contextlib import ExitStack
from hashlib import sha256
from heapq import merge
from itertools import groupby
import json
from math import comb
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from inventory import HERE, build_input, maximal_rectangles, require, six_rectangles
from patterns import low_sets
from rectangles import ROWS, covered_rows

WORK = {
    'three':(10,'all',comb(25067,3),6),
    'three-small':(11,'small',comb(25067,3)-comb(24920,3),6),
    'four-two-small':(9,'four',sum(comb(147,h)*comb(24920,4-h) for h in range(2,5)),24),
    'four-one-small':(9,'four-one',147*comb(24920,3),24),
}
CONTROLS = [[4,45,69,77,98,117,135,146,162],[19,31,37,73,75,98,145,162,167],
            [2,3,7,25,33,77,82,128,132,146],[0,9,22,33,79,87,100,143,152,167],
            [11,32,33,41,43,48,61,68,88,108,109,126,140,152,157,160]]
FIELDS = ['representatives','physical_weight','eligible_thirds_or_fourths','local_sum',
          'domination','parity','other_degree_constraints','admitting_profiles','profiles','search_nodes']


def compile_program(name,tmp):
    path=tmp/name
    subprocess.run(['c++','-O3','-std=c++20',str(HERE/(name+'.cpp')),'-o',str(path)],check=True)
    return path


def reject_or_validate(line):
    kind,*items=line.split()
    if kind.startswith('COVER'):
        anchor,*values=map(int,items)
        size=4 if kind=='COVER4' else 3
        ids,hs=values[:size],values[size:]
        members=[(a,b) for _,a,b in sorted((a|b<<21,a,b) for a,b in maximal_rectangles() if a.bit_count()*b.bit_count()!=36)]
        maximum=six_rectangles()
        require(len(set(ids))==len(ids) and len(set(hs))==len(hs),'Repeated cover member')
        boxes=[members[i] for i in ids]+[maximum[i] for i in hs]
        require(covered_rows(boxes)==list(ROWS),'Proposed cover fails on the posted matrix')
        raise RuntimeError(f'Complete size-{len(boxes)} cover in root {anchor}: {boxes}')
    return kind,list(map(int,items))


def merged_lines(files,key):
    with ExitStack() as stack:
        streams=[stack.enter_context(p.open()) for p in files]
        yield from merge(*streams,key=key)


def audit_search(mode,files,compare=None):
    m,action,expected,denominator=WORK[mode]
    four=action.startswith('four')
    def key(s):
        words=s.split(maxsplit=3)
        return int(words[1]),int(words[2]) if four else -1
    sums=Counter();global_hash=sha256();anchors={};previous=None;records=0;positive_prefixes=[]
    for anchor,lines in groupby(merged_lines(files,key),key=lambda s:key(s)[0]):
        block=sha256();blocks=0
        for line in lines:
            kind,v=reject_or_validate(line)
            require(kind==('QUAD' if four else 'PAIR') and len(v)==(13 if four else 12),'Malformed case receipt')
            order=key(line)
            require(previous is None or previous<order,'Results are repeated or out of order')
            previous=order;records+=1;blocks+=1
            n,mass,eligible,stamp,*counts=v[2 if four else 1:]
            require(n==sum(counts[:5]) and 0<=n<=eligible and 0<=stamp<2**64,'Incomplete case decisions')
            for name,x in zip(FIELDS,[n,mass,eligible,*counts]):sums[name]+=x
            global_hash.update(line.encode());block.update(line.encode())
            if four and counts[-3]:
                positive_prefixes.append([1 if mode=='four-one-small' else 2,anchor,v[1],counts[-3],counts[-2]])
            if compare is not None and anchor in compare:
                r=compare[anchor]
                require([n,mass,counts[-2]]==[r['cases'],r['physical_weight_sixths'],r['profiles']],
                        'The earlier solver disagrees about a marked pair')
        anchors[anchor]=(blocks,block.hexdigest())
    require(sums['physical_weight']==denominator*expected,'Incorrect physical orbit mass')
    require(four or set(anchors)==set(range(2487)),'Missing marked pair')
    if four:
        require(len(anchors)==(9 if mode=='four-two-small' else 99),'Missing marked small/large pairs')
        if (HERE/'four-prefixes.tsv').is_file():
            marking=1 if mode=='four-one-small' else 2
            table=[list(map(int,s.split())) for s in (HERE/'four-prefixes.tsv').read_text().splitlines()]
            require(positive_prefixes==[r for r in table if r[0]==marking],'The independent four-rectangle inputs differ')
    return dict(maximum_rectangles=m,marked_pair_roots=len(anchors),receipt_lines=records,
                physical_unordered_sets=expected,weight_denominator=denominator,**sums,
                canonical_output_sha256=global_hash.hexdigest())


def degrees(family,boxes):
    return [[sum((boxes[i][side]>>v)&1 for i in family) for v in range(21)] for side in (0,1)]


def lights_output(file,m,limit,expected):
    boxes=six_rectangles();hist=defaultdict(Counter);cases=Counter();realized=[];output=sha256()
    seen=set()
    for line in file.read_text().splitlines(keepends=True):
        output.update(line.encode());kind,*rest=line.split()
        p,q,mass,profiles,capped,compatible,nodes,n,*values=map(int,rest)
        require(expected.get((p,q))==mass and (p,q) not in seen,'Dominating-set orbit differs')
        seen.add((p,q));size=p.bit_count()+q.bit_count();cases[size]+=1
        require(compatible<=capped<=profiles,'Wrong profile counts')
        counts=dict(zip(values[:2*n:2],values[1:2*n:2]));ids=values[2*n:]
        if kind=='EXCLUDED':
            require(not counts and not ids,'Malformed exclusion')
            continue
        require(kind=='WITNESS' and counts and len(set(ids))==len(ids)==m,'Malformed extremal example')
        d=degrees(ids,boxes)
        require([sum(1<<i for i,x in enumerate(side) if x<=2) for side in d]==[p,q],'Wrong low labels')
        cells=sum(w.bit_count() for w in covered_rows([boxes[i] for i in ids]))
        require(cells==max(counts),'Extremal witness disagrees with its histogram')
        for cells,num in counts.items():hist[size][cells]+=num*mass
        realized.append(dict(rows=p,cols=q,low_labels=size,orbit_size=mass,profiles=profiles,capped=capped,
                             incident_pair_bound=compatible,families_per_marking=sum(counts.values()),
                             maximum_covered=max(counts),witness=ids))
    require(seen=={k for k in expected if sum(w.bit_count() for w in k)<=limit},'A low-label set was omitted')
    return dict(selected=m,degree_threshold=2,at_most_low_labels=limit,
                tested_orbits={str(k):n for k,n in sorted(cases.items())},realized=realized,
                families_by_coverage={str(size):{str(k):n for k,n in sorted(h.items())} for size,h in sorted(hist.items())},
                canonical_output_sha256=output.hexdigest())


def check_controls(text):
    boxes=six_rectangles();report=[];lines=iter(text.splitlines())
    for ids in CONTROLS:
        original=covered_rows([boxes[j] for j in ids])
        for kind in (['EXACT','SEARCH'] if len(ids)<=10 else ['EXACT']):
            line=next(lines).split()
            k=3 if kind=='EXACT' else 4
            found=list(map(int,line[k:]))
            require(line[0]==kind and len(found)==len(set(found))==len(ids),'Invalid positive control')
            cover=covered_rows([boxes[j] for j in found])
            require(all(not(a&~b) for a,b in zip(original,cover)),'Incomplete control witness')
            if kind=='EXACT':require(degrees(found,boxes)==degrees(ids,boxes),'The prescribed profile differs')
            report.append(dict(mode=kind,required_cells=sum(w.bit_count() for w in original),
                               selected=len(ids),witness=found))
    require(next(lines,None) is None,'Unexpected control output')
    return report


def compute(mode,tmp,jobs,core):
    data=build_input()
    board=tmp/'inventory';board.write_text(data)
    if mode in WORK:
        m,action,_,_=WORK[mode]
        scanner=compile_program('scan',tmp)
        def task(k):
            output=tmp/f'scan-{k}.out'
            args=[str(scanner),str(board),str(m),str(k),'2487',str(jobs),action]
            if core:args.append(str(tmp/f'core-{k}.txt'))
            with output.open('w') as file:subprocess.run(args,stdout=file,check=True)
            return output
        with ThreadPoolExecutor(max_workers=jobs) as pool:files=list(pool.map(task,range(jobs)))
        compare=None
        prior=HERE/'resume/three-at-13/decisions.json'
        if mode=='three' and prior.is_file():
            compare={r['pair_case']:r for r in json.loads(prior.read_text())['excluded']}
        result=audit_search(mode,files,compare)
        if core:
            paths=[tmp/f'core-{k}.txt' for k in range(jobs)]
            with core.open('w') as out:
                out.writelines(merged_lines(paths,lambda s:tuple(map(int,s.split()[:2]))))
    elif mode=='lights':
        rows=low_sets(11);inp=tmp/'low-sets'
        inp.write_text(''.join(' '.join(map(str,row))+'\n' for row in rows))
        solver=compile_program('patterns',tmp);result={}
        for m,limit in [(9,11),(10,8)]:
            path=tmp/f'lights-{m}.out'
            with path.open('w') as out:subprocess.run([solver,board,inp,str(m),str(limit)],stdout=out,check=True)
            result[str(m)]=lights_output(path,m,limit,{(p,q):n for p,q,n in rows})
    else:
        solver=compile_program('controls',tmp)
        inp=''.join(' '.join(map(str,[len(ids),*ids]))+'\n' for ids in CONTROLS)
        result=check_controls(subprocess.check_output([solver,board],input=inp,text=True))
    return dict(inventory_sha256=sha256(data.encode()).hexdigest(),result=result)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode',choices=[*WORK,'lights','controls'])
    ap.add_argument('--jobs',type=int,default=1)
    ap.add_argument('--residuals',type=Path,help='Write the still-feasible numerical inputs for the independent size-13 replay')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    require(args.jobs>0 and (not args.residuals or args.mode=='three'),'Invalid replay option')
    with TemporaryDirectory() as folder:report=compute(args.mode,Path(folder),args.jobs,args.residuals)
    if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')
    else:require(report==json.loads((HERE/'results.json').read_text())[args.mode],'Published receipt differs')
    print(args.mode,'verified')
