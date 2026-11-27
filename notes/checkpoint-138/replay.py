"""Replay the two-exception and one-hole searches from the original board."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent/'checkpoint-137'
sys.path.insert(0,str(PRIOR))
from pairs import inventory, pair_boxes
from rectangles import ROWS, bits, case_orbits, covered_rows, group, label_patterns, perm_mask, require, six_rectangles


def line(values):
    return ' '.join(map(str,values))+'\n'


def prefix(boxes):
    return line(ROWS)+''.join(line(box) for box in boxes)


def digest(s):
    return sha256(s.encode()).hexdigest()


def execute(binary, board, cases, jobs):
    """Initialize the unchanged board once for each disjoint batch of cases."""
    jobs = min(jobs,len(cases))
    def run(indices):
        batch = board+''.join(cases[i] for i in indices)
        output = subprocess.check_output([binary],input=batch,text=True).splitlines()
        require(len(output)==len(indices),'Incomplete search output')
        return [(i,row.split()) for i,row in zip(indices,output)]
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        batches = pool.map(run,[range(i,len(cases),jobs) for i in range(jobs)])
        return [row for _,row in sorted(pair for batch in batches for pair in batch)]


def excluded(out, fields):
    for i,row in enumerate(out):
        require(len(row)==1+fields and row[0]=='EXCLUDED',
                f'Case {i} returned {row}; check the reported rectangle IDs')
    return [list(map(int,row[1:])) for row in out]


def build(source, directory):
    binary = directory/source.stem
    subprocess.run(['c++','-O3','-std=c++20',str(source),'-o',str(binary)],check=True)
    return binary


def case(budget, minimum, hole, fixed_label, seeds, surplus, fill):
    return line([budget,minimum,hole,fixed_label,len(seeds),surplus,*seeds])+line(fill)


def controls(binary, boxes):
    known = json.loads((PRIOR/'witnesses.json').read_text())
    full = [boxes.index(tuple(w)) for w in known['cover_16']]
    near = [boxes.index(tuple(w)) for w in known['near_15']]
    holes = [(i,j) for i,(actual,want) in enumerate(zip(covered_rows(known['near_15']),ROWS))
             for j in bits(want & ~actual)]
    require(holes==[(8,16),(10,16)],'The positive control differs')
    hole_fill = [0]*21
    for i,j in holes:
        hole_fill[i] |= 1<<j
    # Omit one selected rectangle in each positive example so the solver must recover coverage.
    twelve = full[:12]
    synthetic = [a & ~b for a,b in zip(ROWS,covered_rows([boxes[k] for k in twelve]))]
    tests = [(16,-1,full[:-1],[0]*21),(15,21*8+16,near[:-1],hole_fill),
             (12,-1,twelve[:-1],synthetic)]
    inputs = [case(n,0,h,-1,s,-1,f) for n,h,s,f in tests]
    raw = execute(binary,prefix(boxes),inputs,1)
    results = []
    for (limit,hole,seeds,fill),row in zip(tests,raw):
        require(row[0]=='COVER','Missing positive control')
        ids = list(map(int,row[3:]))
        require(len(ids)==len(set(ids))<=limit and set(seeds)<=set(ids)
                and all(0<=j<len(boxes) for j in ids),'Invalid positive family')
        hit = covered_rows([boxes[j] for j in ids])
        require([a|b for a,b in zip(hit,fill)]==list(ROWS),'Incorrect positive coverage')
        require(hole<0 or not (hit[hole//21]>>(hole%21)&1),'Distinguished hole was covered')
        require(len(ids)>len(seeds),'Positive control did not exercise the search')
        results.append(dict(ids=ids,states=int(row[1]),profiles=int(row[2])))
    return results


def pairs_report(binary, boxes, jobs):
    pairs,mass = inventory()
    inputs = [case(12,0,-1,-1,[],-1,covered_rows(pair_boxes(p))) for p in pairs]
    counts = excluded(execute(binary,prefix(boxes),inputs,jobs),2)
    require(len(counts)==2487 and all(n>0 and q>0 for n,q in counts),'Unexpected pair inventory')
    return dict(budget=14,hexads_available=12,representatives=len(counts),
                physical_unordered_pairs=25067*25066//2,orientation_weighted_pairs=mass,
                inventory_sha256=digest(json.dumps(pairs,separators=(',',':'))),
                input_sha256=digest(prefix(boxes)+''.join(inputs)),
                total_states=sum(n for n,q in counts),total_root_profiles=sum(q for n,q in counts),
                decisions=counts)


def near_inputs(boxes):
    # The hole is the zero in row 0, column 1. A group element is a permutation of 42 labels.
    z = 1 | (1<<22)
    words = [a | b<<21 for a,b in boxes]
    index = {w:i for i,w in enumerate(words)}
    elements = group()
    orbit = {(1<<g[0]) | (1<<g[22]) for g in elements}
    require(orbit=={(1<<i) | (1<<(21+j)) for i,m in enumerate(ROWS) for j in bits(m)},
            'The board group does not reach every hole')
    maps = [(g,perm_mask(g)) for g in elements if ((1<<g[0]) | (1<<g[22]))==z]
    require(len(maps)==720,'Incorrect hole stabilizer')
    _,triples = label_patterns(boxes)
    tight = case_orbits([(i,t) for i in range(42) if not (z>>i&1) for t in triples[i]],
                        [(g,[index[move(w)] for w in words]) for g,move in maps])
    left = set(words)
    surplus = []
    while left:
        w = min(left)
        orbit = {move(w) for _,move in maps}
        require(w in orbit and orbit<=left,'Surplus orbits overlap')
        left -= orbit
        surplus.append(dict(id=index[w],multiplicity=len(orbit)))
    require(len(tight)==8 and sum(t['multiplicity'] for t in tight)==3840,'Wrong tight cases')
    require(len(surplus)==3 and sum(t['multiplicity'] for t in surplus)==168,'Wrong surplus cases')
    fill = [2]+[0]*20
    old = [line([15,0,t['label'],3,*t['ids']])+line(fill) for t in tight]
    new = [case(15,4,1,-1,[],t['id'],fill) for t in surplus]
    return tight,surplus,old,new


def near_report(binary, previous, boxes, jobs):
    tight,surplus,old,new = near_inputs(boxes)
    board = prefix(boxes)
    counts = excluded(execute(previous,board,old,jobs),1)
    for record,(n,) in zip(tight,counts):
        record['states'] = n
    counts = excluded(execute(binary,board,new,jobs),2)
    for record,(n,q) in zip(surplus,counts):
        require(q==1,'Specified surplus does not select exactly one profile')
        record.update(states=n,profiles=q)
    return dict(hole=[0,1],tight=tight,surplus=surplus,
                tight_input_sha256=digest(board+''.join(old)),
                surplus_input_sha256=digest(board+''.join(new)),
                total_states=sum(r['states'] for r in tight+surplus),positive_controls=controls(binary,boxes))


def whole_report(binary,boxes):
    data = case(15,4,1,-1,[],-1,[2]+[0]*20)
    out = excluded(execute(binary,prefix(boxes),[data],1),2)
    require(out[0][1]==168,'The unrestricted degree-profile inventory differs')
    return dict(states=out[0][0],profiles=out[0][1],input_sha256=digest(prefix(boxes)+data))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['pairs','near','whole'])
    parser.add_argument('--jobs',type=int,default=1)
    parser.add_argument('--output',type=Path,help='Write a new receipt instead of comparing the published receipt')
    args = parser.parse_args()
    require(args.jobs>=1,'At least one worker is required')
    with TemporaryDirectory() as temp:
        boxes = six_rectangles()
        directory = Path(temp)
        binary = build(HERE/'degree_search.cpp',directory)
        if args.mode=='near':
            result = near_report(binary,build(PRIOR/'hexads.cpp',directory),boxes,args.jobs)
        elif args.mode=='pairs':
            result = pairs_report(binary,boxes,args.jobs)
        else:
            result = whole_report(binary,boxes)
    # Keep thousands of individual numerical decisions on one line each.
    value = json.dumps(result,indent=2)
    if args.mode=='pairs':
        import re
        value = re.sub(r'\[\s+(\d+),\s+(\d+)\s+\]',r'[\1, \2]',value)
    if args.output:
        args.output.write_text(value+'\n')
    else:
        reference = json.loads((HERE/(args.mode+'.json')).read_text())
        require(reference==result,'Calculated receipt differs from the published receipt')
    count = result['representatives'] if args.mode=='pairs' else (
        len(result['tight'])+len(result['surplus']) if args.mode=='near' else 1)
    print(args.mode,result.get('total_states',result.get('states')),'states,',count,'search cases')
