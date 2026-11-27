"""Rebuild the finite cases and reproduce every recorded search decision."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from rectangles import HERE, ROWS, bits, covered_rows, reconstruct, require


def witness_record(boxes):
    source = json.loads((HERE/'witnesses.json').read_text())
    report = {}
    for name, family in source.items():
        require(len(set(map(tuple, family))) == len(family) and
                all(tuple(box) in boxes for box in family), 'Invalid six-by-six witness')
        covered = covered_rows(family)
        holes = [[i,j] for i in range(21) for j in bits(ROWS[i] & ~covered[i])]
        report[name] = dict(rectangles=len(family), covered=336-len(holes), holes=holes)
    require(report['cover_16']['covered'] == 336 and report['near_15']['covered'] == 334,
            'Published witnesses differ')
    return report


def solve(binary, prefix, budget, fill, cases):
    payload = prefix
    for mode,label,ids in cases:
        args = [budget,mode,label,len(ids),*ids]
        payload += ' '.join(map(str,args))+'\n'+' '.join(map(str,fill))+'\n'
    response = subprocess.check_output([binary],input=payload,text=True).splitlines()
    require(len(cases) == len(response), 'Missing exact decision')
    decisions = []
    for line in response:
        outcome, states, *ids = line.split()
        require(outcome == 'EXCLUDED' and int(states) > 0 and not ids, 'Cover found or invalid result: '+line)
        decisions.append(int(states))
    return dict(cases=len(response),states=decisions,input_sha256=sha256(payload.encode()).hexdigest())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--jobs',type=int,default=2)
    ap.add_argument('--output',type=Path,help='Write a reconstructed report to this file')
    args = ap.parse_args()
    require(args.jobs >= 1,'Expected a positive number of workers')
    boxes, geometry = reconstruct()
    witness = witness_record(boxes)
    prefix = ' '.join(map(str,ROWS))+'\n'+''.join(f'{a} {b}\n' for a,b in boxes)
    pure = [(int(len(r['ids']) == 4),r['label'],r['ids']) for r in geometry['pure_roots']]
    tasks = [('pure_triple_15',15,[0]*21,pure[:1]),
             ('pure_quadruples_15',15,[0]*21,pure[1:])]
    for i,orb in enumerate(geometry['shape_orbits']):
        if 'roots' in orb:
            fill = [orb['cols'] if orb['rows'] >> k & 1 else 0 for k in range(21)]
            cases = [(1,-1,[])] + [(0,r['label'],r['ids']) for r in orb['roots']]
            tasks.append((f'one_other_14_{i}',13,fill,cases))
    with TemporaryDirectory() as d:
        binary = str(Path(d)/'hexads')
        subprocess.run(['c++','-std=c++20','-O3',str(HERE/'hexads.cpp'),'-o',binary],check=True)
        def run(task):
            name,budget,fill,cases = task
            result = solve(binary,prefix,budget,fill,cases)
            print(name, result['cases'], sum(result['states']),flush=True)
            return name,result
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            searches = dict(pool.map(run,tasks))
        # Positive controls run through the same search entry point and validate each returned box.
        controls = {}
        family = json.loads((HERE/'witnesses.json').read_text())['cover_16']
        ids = sorted(boxes.index(tuple(b)) for b in family)
        for kept in [15, 16]:
            args16 = [16,0,-1,kept,*ids[:kept]]
            data = prefix+' '.join(map(str,args16))+'\n'+'0 '*21+'\n'
            status,_,*found = subprocess.check_output([binary],input=data,text=True).split()
            found = list(map(int,found))
            require(status == 'COVER' and len(found) <= 16 and set(ids[:kept]) <= set(found) and
                    covered_rows([boxes[i] for i in found]) == list(ROWS),'Positive search control failed')
            controls[str(kept)] = found
    report = dict(geometry=geometry,witnesses=witness,searches=searches,positive_controls=controls)
    rendered = json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.write_text(rendered)
    else:
        require(rendered == (HERE/'results.json').read_text(),'Published numerical receipt differs')
        print('Every finite search and positive control reproduced.')


if __name__ == '__main__':
    main()
