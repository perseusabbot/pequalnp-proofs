"""Check every surviving four-exception profile case with the degree-free solver."""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from inventory import HERE, build_input, group, inventory, maximal_rectangles, require, six_rectangles
from rectangles import bits, covered_rows, perm_mask
from replay import prefix


def replay(prefixes):
    root_bytes=prefixes.read_bytes()
    records=[list(map(int,line.split())) for line in root_bytes.splitlines()]
    pairs,_=inventory()
    words=sorted(a|b<<21 for a,b in maximal_rectangles() if a.bit_count()*b.bit_count()!=36)
    index={w:i for i,w in enumerate(words)}
    elements=group()
    first={}
    stabilizers={}
    for _,anchor,c,_,_ in records:
        if anchor in stabilizers:continue
        a,b,_=pairs[anchor]
        if a not in first:
            labels=list(bits(a))
            first[a]=[g for g in elements if all(a>>g[i]&1 for i in labels)]
        labels=list(bits(b))
        stabilizers[anchor]=[g for g in first[a] if all(b>>g[i]&1 for i in labels)]
    canonical=[]
    with TemporaryDirectory() as tmp:
        tmp=Path(tmp);board=tmp/'board';board.write_text(build_input())
        triples=tmp/'prefixes'
        with triples.open('w') as out:
            for n,anchor,c,_,_ in records:
                a,b,_=pairs[anchor]
                print(n,anchor,index[a],index[b],c,file=out)
        binary=tmp/'filter'
        subprocess.run(['c++','-O3','-std=c++20',str(HERE/'four_filter.cpp'),'-o',str(binary)],check=True)
        raw=subprocess.check_output([binary,board,triples],text=True)
        possible=defaultdict(dict)
        for line in raw.splitlines():
            n,anchor,c,d,count=map(int,line.split())
            possible[n,anchor,c][d]=count
        for n,anchor,c,cases,profiles in records:
            left=possible.pop((n,anchor,c))
            labels=list(bits(words[c]))
            maps=[perm_mask(g) for g in stabilizers[anchor] if all(words[c]>>g[i]&1 for i in labels)]
            total=found=0
            while left:
                d=min(left);count=left[d]
                orbit={index[move(words[d])] for move in maps}
                require(d in orbit and all(left[k]==count for k in orbit),'Incomplete survivor orbit')
                for k in orbit:del left[k]
                total+=count;found+=1;canonical.append((anchor,c,d))
            require((found,total)==(cases,profiles),'Fourth-rectangle profile inventory differs')
        require(not possible,'Unexpected positive prefix')
        prior=HERE.parent/'checkpoint-137/hexads.cpp';solver=tmp/'old'
        subprocess.run(['c++','-O3','-std=c++20',str(prior),'-o',str(solver)],check=True)
        text=prefix(six_rectangles());inputs=[]
        for anchor,c,d in canonical:
            a,b,_=pairs[anchor]
            fill=covered_rows([(w&((1<<21)-1),w>>21) for w in [a,b,words[c],words[d]]])
            inputs.append('9 0 -1 0\n'+' '.join(map(str,fill))+'\n')
        out=subprocess.check_output([solver],input=text+''.join(inputs),text=True)
        lines=[s.split() for s in out.splitlines()]
        require(len(lines)==len(canonical) and all(len(v)==2 and v[0]=='EXCLUDED' for v in lines),'Independent four-rectangle cover result differs')
    return dict(prefixes=len(records),prefix_sha256=sha256(root_bytes).hexdigest(),physical_residuals=len(raw.splitlines()),
                distinct_representatives_checked=len(canonical),prior_solver_sha256=sha256(prior.read_bytes()).hexdigest(),
                prior_states=sum(int(k[1]) for k in lines),output_sha256=sha256(out.encode()).hexdigest())


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    result=replay(HERE/'four-prefixes.tsv')
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    else:require(result==json.loads((HERE/'four-reference.json').read_text()),'Independent receipt differs')
    print(result['distinct_representatives_checked'],'four-exception residuals excluded independently')
