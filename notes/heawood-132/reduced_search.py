"""Search the 15-input residual problem and lift any positive answer directly to opening 20."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from completion import CENTER, DOMAIN, MASK, inputs, lift
from deletion_tables import HERE
from geometry131 import GROUP, column, encode, moved, parent_floors, read, require, sample


def instance(cap):
    jobs=read(HERE/'projections.json')
    known=parent_floors()
    known[128895,11679]=16
    for checkpoint in (HERE.parent/'heawood-131',HERE):
        for r in read(checkpoint/'results.json')['decisions']:
            require(not r['possible'],'Unsupported projection floor')
            key=r['mask'],r['vertices']
            known[key]=max(known.get(key,0),r['cap']+1)
    root=sample(MASK,DOMAIN)
    tests=[]
    seen=set()
    for t,L in [(DOMAIN,22),(8127,20)]:
        model=sample(MASK,t)
        for _,p in GROUP:
            domain=moved(t,p)
            if domain in seen or domain&~DOMAIN:
                continue
            positive={moved(r,p) for r in model['positive_rows']}
            palette={0}|{moved(r,p) for r in model['signals']}
            if not positive<=set(root['positive_rows']) or any((s&domain) not in palette for s in root['signals']):
                continue
            negatives=sorted(moved(n,p) for n in model['negative_rows'])
            lifts=[next(r for r in root['negative_rows'] if r&domain==n) for n in negatives]
            tests.append(dict(source=[MASK,t,L],permutation=list(p),negative_lifts=lifts))
            seen.add(domain)
    older=next(j for j in jobs if (j['mask'],j['vertices'],j['cap'])==(MASK,DOMAIN,21))
    tests=(tests+older['tests'])[:64]
    raw=encode(dict(mask=MASK,vertices=DOMAIN,cap=cap,tests=tests),known).splitlines()
    ports=inputs((8,9))
    observed=root['positive_rows']+root['negative_rows']
    columns=[column(s,observed) for s in ports]
    require(len(ports)==15 and set(ports)<set(root['signals']),'Wrong reduced alphabet')
    raw[0]=' '.join(map(str,[cap,len(root['positive_rows']),len(root['negative_rows']),len(ports),len(tests)]))
    raw[1]=' '.join(map(str,columns))
    group=set()
    for _,p in GROUP:
        action=[moved(s,p) for s in ports]
        if p[CENTER]==CENTER and set(action)==set(ports):
            group.add(tuple(ports.index(s) for s in action))
    raw.append(str(len(group)))
    raw.extend(' '.join(map(str,p)) for p in sorted(group))
    return '\n'.join(raw)+'\n',columns


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cap',choices=[21,22,23],type=int,default=22)
    ap.add_argument('--emit',action='store_true',help='print the validated solver input')
    args=ap.parse_args()
    data,columns=instance(args.cap)
    if args.emit:
        print(data,end='')
        return
    with tempfile.TemporaryDirectory() as temp:
        solver=Path(temp)/'search'
        subprocess.run(['c++','-O3','-std=c++17','-Wall','-Wextra','-pedantic',str(HERE/'symmetry_search.cpp'),
                        '-o',str(solver)],check=True)
        first,*proof=subprocess.check_output([solver],text=True,input=data).splitlines()
    answer,roots,states=first.split()
    require(answer in ('YES','NO'),'Incomplete reduced search')
    if answer=='NO':
        require(not proof,'Unexpected negative witness')
        print(f'No circuit through {args.cap} gates. Exhausted {states} states across {roots} supports.')
        return
    gates=[]
    for line in proof:
        a,b,op,z=map(int,line.split())
        require(op in (0,1) and z==(a|b if op else a&b),'Incorrect gate')
        gates.append(['OR' if op else 'AND',columns.index(a),columns.index(b)])
        columns.append(z)
    require(len(gates)<=args.cap,'Over-budget positive search result')
    print(json.dumps(lift(gates),indent=1))


if __name__=='__main__':
    main()
