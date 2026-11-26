"""Check the duality and count the incumbent subsets excluded by local coloring."""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from math import comb
import os
from pathlib import Path
import subprocess
import tempfile

from geometry import ACTIONS, HERE, ROWS, bits, group, require
from radius import instance
from search import encode


def local_counts(boxes,elements,k):
    index={encode(box):i for i,box in enumerate(boxes)}
    sites=[tuple(bits(w)) for w in index]
    powers=[1<<j for j in range(42)]
    subsets=[sum(1<<i for i in c) for c in combinations(range(14),k)]
    sets=set(subsets)
    parents={s:s for s in subsets}
    returns=Counter()
    stabilizers=Counter()
    def root(a):
        while a!=parents[a]:
            parents[a]=parents[parents[a]]
            a=parents[a]
        return a
    for g in elements:
        dest={}
        for i,v in enumerate(sites):
            word=sum(powers[g[x]] for x in v)
            if word in index:
                dest[i]=index[word]
        if len(dest)<k:
            continue
        returns[sum(1<<j for j in dest)]+=1
        for choice in combinations(dest,k):
            a=sum(1<<j for j in choice)
            b=sum(1<<dest[j] for j in choice)
            if a==b:
                stabilizers[a]+=1
            parents[root(b)]=root(a)
    representatives={root(a) for a in sets}
    stabs=Counter(stabilizers[i] for i in representatives)
    require(all(s>0 and len(elements)%s==0 for s in stabs),'Invalid subset stabilizer')
    total=sum(count*(len(elements)//s) for s,count in stabs.items())
    # A second derivation uses only the number of group maps returning a subset to the seed.
    total2=sum(Fraction(len(elements),sum(k for mask,k in returns.items() if mask&s==s)) for s in sets)
    require(total2==total,'Independent incidence total differs')
    return dict(seed_subsets=len(sets),subset_orbits=len(representatives),by_stabilizer=dict(sorted(stabs.items())),
                distinct_images=total)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--solve',choices=['fixed','any','both'],help='Run exhaustive coloring as well')
    ap.add_argument('--radius',type=int,choices=range(1,15),help='Override the documented search radius')
    args=ap.parse_args()
    boxes=json.loads((HERE.parent/'checkpoint-133'/'plane-examples.json').read_text())['unrestricted']['rectangles']
    a=ACTIONS['dualities']['orthogonal']['columns_for_rows']
    require(sorted(a)==list(range(21)),'Invalid polarity')
    b=[a.index(i) for i in range(21)]
    require(all(ROWS[x]>>j&1==ROWS[b[j]]>>a[x]&1 for x in range(21) for j in range(21)),'Polarity changes board')
    dual=lambda rect:(sum(1<<b[j] for j in bits(rect[1])),sum(1<<a[i] for i in bits(rect[0])))
    perm=[boxes.index(list(dual(rect))) for rect in boxes]
    require(all(perm[perm[i]]==i for i in range(14)),'Dual does not preserve the seed')
    require((b[18],a[6])==(13,10) and (b[10],a[13])==(6,18),'Holes not exchanged')
    elements=group()
    result=dict(rectangle_permutation=perm,fixed_rectangles=sum(i==j for i,j in enumerate(perm)),
                holes=[[6,18],[13,10]],seven=local_counts(boxes,elements,7))
    if args.solve:
        with tempfile.TemporaryDirectory() as tmp:
            binary=Path(tmp)/'nearcover'
            subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(HERE/'nearcover.cpp'),'-o',str(binary)],check=True)
            for name,k,opts in [('fixed',8,['--hole','13','10']),('any',7,['--any-hole'])]:
                if args.solve not in (name,'both'):
                    continue
                radius=args.radius or k
                output=subprocess.check_output([str(binary),*opts],input=instance(radius)).decode().strip()
                if output.startswith('EXCLUDED'):
                    tag,r,windows,states,largest=output.split()
                    require(int(r)==radius and int(windows)==comb(14,radius),'Incomplete replacement enumeration')
                    result[name]=dict(radius=radius,subsets=int(windows),states=int(states),largest=int(largest))
                else:
                    require(output.startswith('COVER'),'Unrecognized solver result')
                    result[name]=dict(radius=radius,witness=output)
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
