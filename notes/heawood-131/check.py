"""Replay the signed searches, their input reductions, controls, and the orbit census."""
import argparse
from copy import deepcopy
from concurrent.futures import ThreadPoolExecutor
from functools import cache
from itertools import combinations
import json
import subprocess
import sys
import tempfile

from pathlib import Path

from geometry131 import HERE, column, encode, parent_floors, read, require, sample, serial_cases
from inventory import inventory
from row_tables import controls
sys.path.insert(0, str(HERE.parent/'heawood-129'))
from verify import compile_engines, run_both


def compile_signed(where):
    binary = where/'signed_search'
    subprocess.run(['c++','-std=c++17','-O3','-Wall','-Wextra','-pedantic',str(HERE/'signed_search.cpp'),
                    '-o',str(binary)],check=True)
    return binary


def run_search(binary, contents):
    first,*proof = subprocess.check_output([binary],input=contents,text=True).splitlines()
    outcome,roots,nodes = first.split()
    require(outcome in ('YES','NO'),'Incomplete circuit search')
    cap,positives,_,_,_ = map(int,contents.splitlines()[0].split())
    if outcome=='YES':
        available = set(map(int,contents.splitlines()[1].split()))
        require(len(proof)<=cap,'Over-budget positive control')
        for line in proof:
            a,b,op,z = map(int,line.split())
            require(a in available and b in available and op in (0,1),'Unknown wire in witness')
            require(z==(a|b if op else a&b),'Incorrect gate in witness')
            available.add(z)
        require((1<<positives)-1 in available,'Witness misses the output')
    else:
        require(not proof,'Unexpected circuit in a negative result')
    return dict(possible=outcome=='YES',root_supports=int(roots),expanded_states=int(nodes))


@cache
def tiny_outputs():
    # All three-variable circuits through four gates, with all old wires available.
    prim = frozenset(sum(1<<r for r in range(8) if r>>i&1) for i in range(3))
    states = {prim}
    floor = {}
    for cost in range(5):
        for wires in states:
            for w in wires:
                floor.setdefault(w,cost)
        if cost<4:
            states = {wires|{z} for wires in states for a,b in combinations(wires,2)
                      for z in (a&b,a|b) if z not in wires}
    require(len(floor)==18,'Incomplete three-variable control family')
    return floor


def exhaustive_controls(binary):
    floor = tiny_outputs()
    results = []
    for truth,minimum in sorted(floor.items()):
        pos = [r for r in range(8) if truth>>r&1]
        neg = [r for r in range(8) if not truth>>r&1]
        rows = pos+neg
        literals = [column(1<<v,rows) for v in range(3)]
        # The local answer can be read independently from all reachable truth tables.
        tests = []
        for i in range(len(pos)):
            for j in range(len(neg)):
                p = [v for h,v in enumerate(pos) if h!=i]
                n = [v for h,v in enumerate(neg) if h!=j]
                if not p or not n:
                    continue
                lower = min(cost for sig,cost in floor.items()
                            if all(sig>>v&1 for v in p) and all(not(sig>>v&1) for v in n))
                P = sum(1<<rows.index(v) for v in p)
                N = sum(1<<rows.index(v) for v in n)
                tests.append([lower,P,N,*literals])
        for cap in sorted({max(0,minimum-1),minimum}):
            for projected in (False,True):
                selected = tests if projected else []
                header = [cap,len(pos),len(neg),len(literals),len(selected)]
                chunks = [header,literals]
                for low,P,N,*free in selected:
                    chunks.extend([[low,P,N,len(free)],free])
                raw = ''.join(' '.join(map(str,x))+'\n' for x in chunks)
                result = run_search(binary,raw)
                require(result['possible']==(cap>=minimum),'Tiny exhaustive oracle disagrees')
                results.append([truth,cap,projected,result['possible']])
    return results


def corrupt_controls(probe,known):
    rejected = []
    for change in ('unproved lower bound','repeated permutation entry','missing negative lift','incorrect lift'):
        item = deepcopy(probe)
        test = item['tests'][0]
        if change=='unproved lower bound':
            test['source'][2] += 100
        elif change=='repeated permutation entry':
            test['permutation'][0] = test['permutation'][1]
        elif change=='missing negative lift':
            test['negative_lifts'].pop()
        else:
            test['negative_lifts'][0] = 0
        try:
            encode(item,known)
        except ValueError:
            rejected.append(change)
        else:
            raise ValueError('Accepted damaged projection')
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='regenerate the published numerical receipts')
    parser.add_argument('--use-basis-receipt',action='store_true',
                        help='use the recorded result of the separate ten-vertex searches')
    parser.add_argument('--jobs',type=int,default=1,help='number of signed searches to run at once')
    args = parser.parse_args()
    require(args.jobs>0,'Expected a positive number of workers')
    known = parent_floors()
    small_case = sample(128895,11679)
    cases = serial_cases()
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        binary = compile_signed(directory)
        if args.use_basis_receipt:
            basis = read(HERE/'basis.json')
        else:
            basis = run_both(compile_engines(directory),small_case,15)
            require(basis==read(HERE/'basis.json'),'Independent ten-vertex searches disagree with receipt')
        require(basis['possible'] is False,'The basis bound fails')
        known[(128895,11679)] = 16
        tested = exhaustive_controls(binary)
        rejected = corrupt_controls(cases[0],known)
        # Each projection may cite only a prior decision. They can execute in
        # parallel because the report is accepted only if every decision succeeds.
        inputs = []
        for job in cases:
            m,t,k = job['mask'],job['vertices'],job['cap']
            inputs.append((job,encode(job,known)))
            known[m,t] = max(known.get((m,t),0),k+1)

        def decide(task):
            job, contents = task
            answer = run_search(binary,contents)
            require(not answer['possible'],'A proposed lower bound admits a circuit')
            return dict(mask=job['mask'],vertices=job['vertices'],cap=job['cap'],
                        local_restrictions=len(job['tests']),**answer)

        with ThreadPoolExecutor(args.jobs) as pool:
            decisions = list(pool.map(decide,inputs))
        for d in decisions:
            print(f'Excluded {d["cap"]} gates for ({d["mask"]}, {d["vertices"]}) across '
                  f'{d["root_supports"]} root supports.')
    frontier = inventory(known)
    report = dict(basis=basis,decisions=decisions,oracle_controls=tested,rejected_controls=rejected)
    for name,data in [('results.json',report),('frontier.json',frontier),('controls.json',controls())]:
        if args.write:
            (HERE/name).write_text(json.dumps(data,indent=1)+'\n')
        else:
            require(read(HERE/name)==data,'Published data differs in '+name)
    print(f'{frontier["remaining_masks"]} labeled sets in {frontier["remaining_orbits"]} symmetry classes remain.')


if __name__=='__main__':
    main()
