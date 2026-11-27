"""Verify completed repair runs and independently encode each residual as graph coloring SAT."""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from math import comb
from pathlib import Path
import os
import subprocess
import tempfile

from plane import HERE, ROWS, bits, group, require
from radius import instance
from search import encode

SEED=json.loads((HERE.parent/'checkpoint-133/plane-examples.json').read_text())['unrestricted']['rectangles']


def maps_on_seed(elements):
    index={encode(z):i for i,z in enumerate(SEED)}
    sites=[tuple(bits(w)) for w in index]
    powers=[1<<j for j in range(42)]
    partial=[]
    for g in elements:
        dest=[index.get(sum(powers[g[x]] for x in v),-1) for v in sites]
        if sum(i>=0 for i in dest)>=5:
            partial.append(dest)
    return partial


def anchors(elements, partial, k):
    representatives=[]; intersections={}; inventory=Counter()
    total=0; second=Fraction()
    for subset in combinations(range(14),k):
        mask=sum(1<<i for i in subset)
        images=Counter()
        for perm in partial:
            targets=[perm[i] for i in subset]
            if min(targets)>=0:
                images[sum(1<<j for j in targets)]+=1
        stabilizer=images[mask]
        require(stabilizer>0 and all(n==stabilizer for n in images.values()),'Coset sizes differ')
        rep=min(images)
        intersections[rep]=intersections.get(rep,0)+1
        if mask==rep:
            representatives.append(rep)
            inventory[stabilizer]+=1
            total+=len(elements)//stabilizer
        second+=Fraction(len(elements),sum(images.values()))
    require(total==second and sum(intersections.values())==comb(14,k),'Inconsistent incidence count')
    return sorted(representatives),dict(seed_subsets=comb(14,k),classes=len(representatives),
        by_stabilizer=dict(sorted(inventory.items())),distinct_images=total)


def residual(mask):
    retained=[SEED[i] for i in bits(mask)]
    points=[(p,l) for p,row in enumerate(ROWS) for l in bits(row)
            if not any(a>>p & b>>l & 1 for a,b in retained)]
    edges=[0 for _ in points]
    for i,(p,l) in enumerate(points):
        for j,(q,m) in enumerate(points[:i]):
            if not (ROWS[p]>>m & ROWS[q]>>l & 1):
                edges[i]|=1<<j
                edges[j]|=1<<i
    return points,edges


def clique(edges):
    best=[]
    for first in range(len(edges)):
        result=[first]; allowed=edges[first]
        while allowed:
            v=max(bits(allowed),key=lambda i:((edges[i]&allowed).bit_count(),edges[i].bit_count()))
            result.append(v);allowed&=edges[v]
        if len(result)>len(best):best=result
    return best


def formula(edges,k,allow_one):
    n=len(edges)
    # Names of colors on a clique can be fixed even if one clique vertex is skipped.
    fixed={v:i for i,v in enumerate(clique(edges)[:k])}
    colors=[(fixed[i],) if i in fixed else tuple(range(k)) for i in range(n)]
    var=lambda i,c:k*i+c+1
    deletion=lambda i:n*k+i+1
    prefix=lambda i:n*(k+1)+i+1
    clauses=[]
    for i,cs in enumerate(colors):
        clauses.append([var(i,c) for c in cs]+([deletion(i)] if allow_one else []))
        if allow_one:
            clauses.append([-deletion(i),prefix(i)])
            if i:
                clauses.extend(([-prefix(i-1),prefix(i)],[-prefix(i-1),-deletion(i)]))
    for i,row in enumerate(edges):
        for j in bits(row&((1<<i)-1)):
            for c in set(colors[i]).intersection(colors[j]):
                clauses.append([-var(i,c),-var(j,c)])
    variables=n*(k+(2 if allow_one else 0))
    data=f'p cnf {variables} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
    return data,colors


def sat_case(mask,allow_one,solver):
    pts,edges=residual(mask);k=14-mask.bit_count()
    data,colors=formula(edges,k,allow_one)
    result=subprocess.run([solver,'-q'],input=data,text=True,capture_output=True)
    require(result.returncode in (10,20),'SAT solver did not complete: '+result.stderr[:200])
    if result.returncode==20:
        require('s UNSATISFIABLE' in result.stdout,'Missing UNSAT status')
        return None
    values={int(v) for l in result.stdout.splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0}
    extra=[[0,0] for _ in range(k)]
    for i,(p,l) in enumerate(pts):
        if allow_one and len(pts)*k+i+1 in values:continue
        c=next(c for c in colors[i] if i*k+c+1 in values)
        extra[c][0]|=1<<p; extra[c][1]|=1<<l
    boxes=[SEED[j] for j in bits(mask)]+extra
    occupied=[0]*21
    for a,b in boxes:
        for p in bits(a):occupied[p]|=b
    require(all(not (w&~ROWS[i]) for i,w in enumerate(occupied)),'Illegal reconstructed SAT rectangle')
    covered=sum(w.bit_count() for w in occupied)
    require(covered>=336-int(allow_one),'Incomplete SAT witness')
    return {'rectangles':boxes,'covered':covered}


def check_samples(records,solver):
    for graph,k,allowed,expected in [([6,5,3],2,False,20),([6,5,3],2,True,10),([14,13,11,7],2,True,20)]:
        data,_=formula(graph,k,allowed)
        result=subprocess.run([solver,'-q'],input=data,text=True,capture_output=True)
        require(result.returncode==expected,'Graph coloring control failed')
    for r in records.values():
        sample=r['independent_sample']
        require(sat_case(sample['retained_mask'],bool(r['allowed_holes']),solver) is None,'Unexpected repair found')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sat-samples',action='store_true',help='Independently check one instance from each completed run')
    ap.add_argument('--solver',default='cadical')
    ap.add_argument('--replay-long',action='store_true',help='Repeat both multi-billion-state coloring enumerations')
    args=ap.parse_args()
    records=json.loads((HERE/'repair-runs.json').read_text())
    elements=group();partial=maps_on_seed(elements)
    results={}
    for name,r in records.items():
        k=r['retained'];radius=r['replacements']
        require(k+radius==14,'Incorrect residual budget')
        data=instance(radius)
        require(sha256(data).hexdigest()==r['input_sha256'],'Wrong repair input')
        require(r['solver_output']==f"EXCLUDED {radius} {comb(14,k)} {r['states']} {r['largest']}",'Incomplete original run')
        sample=r['independent_sample']
        pts,graph=residual(sample['retained_mask'])
        cnf,_=formula(graph,radius,bool(r['allowed_holes']))
        require(len(pts)==sample['residual_cells'] and sha256(cnf.encode()).hexdigest()==sample['cnf_sha256'],'Wrong SAT instance')
        _,results[name]=anchors(elements,partial,k)
        if args.replay_long:
            with tempfile.TemporaryDirectory() as temp:
                binary=Path(temp)/'repair'
                source=HERE.parent/('checkpoint-133/repair.cpp' if name=='full' else 'checkpoint-135/nearcover.cpp')
                subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(source),'-o',str(binary)],check=True)
                cmd=[str(binary)]+(['--any-hole'] if r['allowed_holes'] else [])
                require(subprocess.check_output(cmd,input=data).decode().strip()==r['solver_output'],'Full enumeration disagrees')
    if args.sat_samples:check_samples(records,args.solver)
    print(json.dumps(results,indent=2))


if __name__=='__main__':
    main()
