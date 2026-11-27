"""Rebuild the subgroup quotients by two methods and exhaust their integer budgets."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import tempfile

from plane import HERE, ROWS, frame_receipt, group, require
from subgroups import instances, sylow


def compile_program(source,output):
    subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(source),'-o',str(output)],check=True)


def controls(binary):
    # With four slots, the large orbit is the only way to cover all four cells.
    def trial(cap,expected):
        raw=f'4 {cap} 3\n1 1 0\n2 6 0\n4 15 0\n3\n1 1 1 1\n0 0 0 1\n2 0 1 1\n'
        lines=subprocess.check_output([binary],input=raw,text=True).splitlines()
        require(lines[0].split()[0]==expected,'Incorrect weighted cover control')
        if expected=='COVER':
            require(lines[1:]==['4 15 0'],'Incorrect weighted witness')
    trial(3,'EXCLUDED');trial(4,'COVER')
    # A six-cycle exercises the symmetry reduction on a positive and a negative instance.
    # Six singleton masks require six slots. Every cyclic shift preserves all masks.
    ring=''.join(f'1 {1<<i} 0\n' for i in range(6))
    rotations='6\n'+''.join(' '.join(str((i+k)%6) for i in range(6))+'\n' for k in range(6))
    for cap,expected in [(5,'EXCLUDED'),(6,'COVER')]:
        lines=subprocess.check_output([binary],input=f'6 {cap} 6\n'+ring+'0\n'+rotations,text=True).splitlines()
        require(lines[0].split()[0]==expected,'Incorrect symmetric control')
        if expected=='COVER':
            require(sorted(tuple(map(int,s.split())) for s in lines[1:])==[(1,1<<i,0) for i in range(6)],'Incorrect symmetric witness')

    # Compare a weighted cycle with an independent shortest-path calculation on
    # every cell subset, including deliberately asymmetric pruning weights.
    n=8
    sym=[[(a*i+b)%n for i in range(n)] for a in (1,-1) for b in range(n)]
    for masks in [[(1,1),(2,7),(4,255)],[(1,1),(2,17),(2,19),(4,85)],[(1,3),(2,29),(4,31)]]:
        choices={(c,sum(1<<perm[i] for i in range(n) if m>>i&1)) for c,m in masks for perm in sym}
        best=[1000]*(1<<n)
        best[0]=0
        for at in range(1<<n):
            for cost,m in choices:
                best[at|m]=min(best[at|m],best[at]+cost)
        listed=[f'{cost} {m} 0' for cost,m in sorted(choices)]
        hints=['2','0 1 2 0 4 1 0 3','1 0 0 5 1 0 4 0']
        for cap in (best[-1]-1,best[-1]):
            raw='\n'.join([f'{n} {cap} {len(listed)}',*listed,*hints,str(len(sym)),*[' '.join(map(str,t)) for t in sym]])+'\n'
            lines=subprocess.check_output([binary],input=raw,text=True).splitlines()
            expected='COVER' if cap==best[-1] else 'EXCLUDED'
            require(lines[0].split()[0]==expected,'Disagreement with the subset dynamic program')
            if expected=='COVER':
                paid=covered=0
                for line in lines[1:]:
                    price,mask,high=map(int,line.split())
                    require(high==0 and (price,mask) in choices,'Invalid small-board witness')
                    paid+=price
                    covered|=mask
                require(paid<=cap and covered==(1<<n)-1,'Incomplete small-board witness')


def numerical(work,jobs,reference):
    plan=json.loads((HERE/'weights.json').read_text())
    ambient=group();members,product,dual=sylow(ambient)
    fast=work/'profile-check';direct=work/'direct';base=work/'reference'
    compile_program(HERE/'profiles.cpp',fast);compile_program(HERE/'direct.cpp',direct);controls(fast)
    if reference:compile_program(HERE.parent/'checkpoint-135/budget.cpp',base)
    results=dict(frames=frame_receipt(ambient),sylow_order=len(members),legal_nonempty_rectangles=5833331,orders={})
    for order in (8,4):
        folder=work/str(order)
        record=instances(folder,order,ambient,members,product,dual)
        def check(r):
            raw=(folder/f"class-{r['id']}.in").read_text()
            permdata='\n'.join([str(order),' '.join(map(str,ROWS)),
                       *[' '.join(map(str,members[j])) for j in r['subgroup']]])+'\n'
            independent=subprocess.run([direct],input=permdata,text=True,capture_output=True,check=True)
            require(independent.stdout==raw,'Independent quotient masks disagree')
            require(list(map(int,independent.stderr.split()))==[5833331,r['candidate_rectangles']],'Independent rectangle counts disagree')
            proof=plan[str(order)][str(r['id'])]
            n,_,length=raw.splitlines()[0].split()
            budget=proof['budget']
            data=raw.replace(raw.splitlines()[0],f'{n} {budget} {length}',1)
            weights=proof['weights']
            suffix='\n'.join([str(len(weights)),*[' '.join(map(str,w)) for w in weights]])+'\n'
            symmetries=(folder/f"class-{r['id']}.sym").read_text()
            answer=subprocess.check_output([fast],input=data+suffix+symmetries,text=True).splitlines()
            fields=answer[0].split()
            require(len(answer)==1 and len(fields)==3 and fields[0]=='EXCLUDED','A budget was feasible or the decision was incomplete')
            if reference and order==8:
                other=subprocess.check_output([base],input=data,text=True).split()
                require(len(other)==2 and other[0]=='EXCLUDED','Independent budget checker disagrees')
            return dict(**r,excluded_through=budget,profiles=int(fields[1]),search_states=int(fields[2]))
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            record['classes']=list(pool.map(check,record['classes']))
        record['excluded_subgroups']={str(k):sum(r['full_conjugates'] for r in record['classes'] if r['excluded_through']>=k) for k in (13,14,15)}
        results['orders'][str(order)]=record
    divisors={}
    for limit,odd in [(13,945),(14,945),(15,315)]:
        factor=1
        for order in (8,4):
            r=results['orders'][str(order)]
            if r['excluded_subgroups'][str(limit)]==r['subgroups_in_group']:
                factor=max(factor,256//(order//2))
        divisors[str(limit)]=factor*odd
    results['orbit_divisors']=divisors
    results['unrestricted_minimum_interval']=[13,15]
    return results


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--jobs',type=int,default=1)
    ap.add_argument('--reference',action='store_true',help='Repeat all order-eight decisions with the Checkpoint 135 weighted solver')
    ap.add_argument('--write-results',action='store_true')
    args=ap.parse_args()
    if args.jobs<1:raise ValueError('At least one worker is required')
    with tempfile.TemporaryDirectory() as tmp:result=numerical(Path(tmp),args.jobs,args.reference)
    path=HERE/'results.json'
    if args.write_results:path.write_text(json.dumps(result,indent=2)+'\n')
    else:require(json.loads(path.read_text())==result,'Stored results differ from independent replay')
    print(json.dumps(result['orbit_divisors']))


if __name__=='__main__':main()
