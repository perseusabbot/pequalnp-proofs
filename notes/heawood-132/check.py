"""Replay the new Heawood bounds, all six inherited symmetry classes, and the seed decisions."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from itertools import combinations, permutations
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile

from deletion_tables import HERE
from seed_tables import CASES, WIDTH, rows, vertices
from geometry131 import ALL, GROUP, column, encode, moved, parent_floors, read, require, sample
parent_spec=importlib.util.spec_from_file_location('heawood131_check',HERE.parent/'heawood-131'/'check.py')
prior_check=importlib.util.module_from_spec(parent_spec)
parent_spec.loader.exec_module(prior_check)
from inventory import inventory
from row_tables import star_control
from verify import compile_engines, run_both

PARENT=HERE.parent/'heawood-131'


def inherited():
    known=parent_floors()
    known[128895,11679]=16
    for r in read(PARENT/'results.json')['decisions']:
        require(not r['possible'],'Unsupported parent floor')
        key=r['mask'],r['vertices']
        known[key]=max(known.get(key,0),r['cap']+1)
    return known


def group_lines(group):
    return str(len(group))+'\n'+''.join(' '.join(map(str,p))+'\n' for p in sorted(group))


def symmetries(mask,domain):
    model=sample(mask,domain)
    signals=model['signals']
    positions={x:i for i,x in enumerate(signals)}
    positive=set(model['positive_rows'])
    group=set()
    for _,p in GROUP:
        if moved(domain,p)!=domain or {moved(e,p) for e in positive}!=positive:
            continue
        action=[moved(s,p) for s in signals]
        if set(action)==positions.keys():
            group.add(tuple(positions[s] for s in action))
    require(tuple(range(len(signals))) in group,'Missing identity action')
    return group


def symmetry_controls(binary):
    count=0
    for truth,minimum in sorted(prior_check.tiny_outputs().items()):
        pos=[r for r in range(8) if (truth>>r)&1]
        neg=[r for r in range(8) if not (truth>>r)&1]
        group=[p for p in permutations(range(3)) if {moved(r,p) for r in pos}==set(pos)]
        for cap in sorted({minimum,max(0,minimum-1)}):
            prim=[column(1<<v,pos+neg) for v in range(3)]
            raw=f'{cap} {len(pos)} {len(neg)} 3 0\n'+' '.join(map(str,prim))+'\n'
            ans=prior_check.run_search(binary,raw+group_lines(group))
            require(ans['possible']==(cap>=minimum),'Symmetric control disagrees with oracle')
            count+=1
    # This row function is x0. Swapping x0 and x1 is not a signed-row symmetry.
    r=[1,3,5,7,0,2,4,6]
    raw='0 4 4 3 0\n'+' '.join(str(column(1<<v,r)) for v in range(3))+'\n'
    for group in [[(0,1,2),(1,0,2)],[(0,1,2),(0,2,2)],[(0,2,1)]]:
        result=subprocess.run([binary],input=raw+group_lines(group),text=True,capture_output=True)
        require(result.returncode!=0,'Invalid declared symmetry accepted')
    return count


def seed_search(t,cap):
    # Direct evaluation of the recurrence in ThetaSearch. Sorting memo keys only
    # permutes the inputs of a search which tries every unordered pair and both keeps.
    sig=rows(t)
    primary=tuple(sorted(sig[v] for v in vertices(t)))
    full=(1<<WIDTH)-1
    @lru_cache(None)
    def distinction(x):
        return (x & ~(x>>WIDTH)) & full
    @lru_cache(None)
    def visit(k,s):
        if any(distinction(w)==full for w in s):
            return True,1
        expanded=1
        for i,j in combinations(range(len(s)),2):
            rest=list(s)
            b=rest.pop(j)
            a=rest.pop(i)
            covered=0
            for w in rest:
                covered|=distinction(w)
            for z in (a&b,a|b):
                for retained in ([],[a],[b],[a,b]):
                    if len(rest)+1+len(retained)>k:
                        continue
                    separate=covered|distinction(z)
                    for w in retained:
                        separate|=distinction(w)
                    if separate==full:
                        ok,size=visit(k-1,tuple(sorted([z]+retained+rest)))
                        expanded+=size
                        if ok:
                            return True,expanded
        return False,expanded
    ok,paths=visit(cap,primary)
    return dict(possible=ok,distinct_states=visit.cache_info().currsize,unfolded_states=paths)


def new_frontier(known):
    old=read(PARENT/'frontier.json')
    updated=inventory(known)
    result=[]
    for prior,current in zip(old['layers'],updated['layers'],strict=True):
        items={r['representative']:r for r in prior['class_bounds'] if r['gate_floor']<=26}
        current=dict(current)
        records=[dict(r,prior_floor=items[r['representative']]['gate_floor']) for r in current['class_bounds']
                 if r['representative'] in items]
        require({r['representative'] for r in records}==items.keys()
                and set(current['remaining_masks'])<=set(prior['remaining_masks']),'Class inventory mismatch')
        current.update(class_bounds=records,previous_orbits=len(items),previous_masks=prior['remaining'])
        result.append(current)
    updated.update(prior_remaining_masks=old['remaining_masks'],prior_remaining_orbits=old['remaining_orbits'],layers=result)
    def at_budget(layers,gates):
        classes=[r for layer in layers for r in layer['class_bounds'] if r['gate_floor']<=gates]
        return dict(classes=len(classes),labeled_sets=sum(r['size'] for r in classes))
    updated['gate_budgets']={str(g):dict(previous=at_budget(old['layers'],g),current=at_budget(result,g))
                            for g in (24,25,26)}
    return updated


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--jobs',type=int,default=2)
    parser.add_argument('--reference-star',action='store_true',
                        help='also verify the 13-vertex decision with the original per-prefix allowances')
    args=parser.parse_args()
    require(args.jobs>0,'Expected a positive worker count')
    cases=read(HERE/'projections.json')
    known=inherited()
    tasks=[]
    for j in cases:
        m,t,k=(j[n] for n in ('mask','vertices','cap'))
        raw=encode(j,known)
        symmetric=j['engine']=='symmetry'
        require(symmetric or j['engine']=='signed','Unknown search engine')
        group=symmetries(m,t) if symmetric else []
        tasks.append((j,raw+(group_lines(group) if symmetric else ''),len(group)))
        known[m,t]=max(known.get((m,t),0),k+1)
    with tempfile.TemporaryDirectory() as directory:
        temp=Path(directory)
        binary=prior_check.compile_signed(temp)
        sym=temp/'symmetry_search'
        subprocess.run(['c++','-O3','-std=c++17','-Wall','-Wextra','-pedantic',
                        str(HERE/'symmetry_search.cpp'),'-o',str(sym)],check=True)
        engines=compile_engines(temp)
        def solve(task):
            j,raw,order=task
            ans=prior_check.run_search(sym if order else binary,raw)
            require(not ans['possible'],'A proposed lower bound admits a circuit')
            return {**{k:j[k] for k in ('mask','vertices','cap','engine')},'signed_tests':len(j['tests']),
                    'symmetries':order,**ans}
        with ThreadPoolExecutor(args.jobs) as pool:
            decisions=list(pool.map(solve,tasks))
        if args.reference_star:
            raw=next(raw for j,raw,_ in tasks if (j['mask'],j['vertices'],j['cap'])==(262143,16319,21))
            answer=subprocess.check_output([sym,'--reference'],input=raw,text=True).split()
            require(len(answer)==3 and answer[0]=='NO' and int(answer[1])==8,'Reference search disagrees')
            print(f'Reference star search exhausted {answer[2]} states across {answer[1]} supports.',flush=True)
        group_controls=symmetry_controls(sym)
        ordinary=prior_check.exhaustive_controls(sym)
        damaged=prior_check.corrupt_controls(cases[0],inherited())
        seeds=[]
        for t,k in CASES:
            model=sample(ALL,t)
            exact=seed_search(t,k)
            check=run_both(engines,model,k)
            require(not exact['possible'] and not check['possible'] and exact['distinct_states']==check['last_use_states'],
                    'Independent small searches disagree')
            seeds.append(dict(vertices=t,cap=k,positive=len(model['positive_rows']),negative=len(model['negative_rows']),
                              direct=exact,independent=check))
    # Store one explicit star construction at each upper bound. Some instances have two successive lower bounds.
    controls=[]
    for m,t in sorted({(j['mask'],j['vertices']) for j in cases}|{(ALL,t) for t,_ in CASES}):
        model=sample(m,t)
        points=vertices(t)
        edges=model['positive_rows']
        cover=next(n for n in range(1,len(points)+1) if any(
            all(e&sum(1<<v for v in c) for e in edges) for c in combinations(points,n)))
        upper=len(edges)+cover-1
        require(known.get((m,t),0)<=upper,'Lower bound exceeds the verified construction')
        controls.append(star_control(m,t,upper))
    census=new_frontier(known)
    results=dict(decisions=decisions,seeds=seeds,ordinary_controls=len(ordinary),symmetry_controls=group_controls,
                 damaged_symmetries_rejected=3,damaged_projections_rejected=damaged)
    for name,data in [('results.json',results),('frontier.json',census),('controls.json',controls)]:
        if args.write:
            (HERE/name).write_text(json.dumps(data,indent=1)+'\n')
        else:
            require(read(HERE/name)==data,'Replay mismatch in '+name)
    print(f'{len(decisions)} decisions, {len(seeds)} independent seed checks, '
          f'{census["remaining_masks"]} labeled sets in {census["remaining_orbits"]} symmetry classes remain.')


if __name__=='__main__':
    main()
