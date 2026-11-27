"""Cover the board with two exceptional rectangles and the remaining 6-by-6 rectangles."""
import argparse
from datetime import datetime,timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from rectangles import (BOARD, HERE, ROWS, bits, covered_rows, group, maximal_rectangles,
                        perm_mask, require, six_rectangles)
from journal import lock_directory


def atomic(path, value):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value,separators=(',',':'))+'\n')
    temporary.replace(path)


def inventory():
    geometry = json.loads((HERE/'results.json').read_text())['geometry']
    shapes = [r for r in geometry['shape_orbits'] if 'roots' in r]
    groups = {tuple(sorted(s['shape'])): set() for s in shapes}
    for a,b in maximal_rectangles():
        key = tuple(sorted((a.bit_count(),b.bit_count())))
        if key != (6,6):
            groups[key].add(a | b << 21)
    elements = group()
    pairs, total = [], 0
    for i,s in enumerate(shapes):
        root = s['rows'] | s['cols'] << 21
        labels = list(bits(root))
        stabilizer = [perm_mask(g) for g in elements if all(root >> g[l] & 1 for l in labels)]
        require(len(stabilizer) == s['stabilizer'], 'Wrong first-rectangle stabilizer')
        for j in range(i,len(shapes)):
            other = shapes[j]
            candidates = groups[tuple(sorted(other['shape']))]
            require(len(candidates) == other['multiplicity'], 'Shape class differs')
            left = candidates - {root}
            while left:
                mate = min(left)
                orbit = {move(mate) for move in stabilizer}
                require(mate in orbit and orbit <= left,'Malformed second-rectangle orbit')
                left -= orbit
                pairs.append([root,mate,len(orbit)])
                total += len(orbit)*s['multiplicity']
    expected = sum(s['multiplicity']*(s['multiplicity']-1) +
                   s['multiplicity']*sum(t['multiplicity'] for t in shapes[i+1:])
                   for i,s in enumerate(shapes))
    require(expected == total,'Incomplete ordered-pair inventory')
    return pairs,total


def pair_boxes(case):
    return [(w & BOARD,w >> 21) for w in case[:2]]


def confirmed(case, ids, hexads, budget):
    require(len(ids) == len(set(ids)) <= budget and all(0 <= h < len(hexads) for h in ids),
            'Invalid witness indices')
    boxes = [*pair_boxes(case),*[hexads[i] for i in ids]]
    require(covered_rows(boxes) == list(ROWS),'Candidate fails on the posted board')
    return [list(box) for box in boxes]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory',type=Path)
    ap.add_argument('--total',type=int,choices=(13,14),default=13,help='Total number of rectangles allowed')
    ap.add_argument('--stop-after',type=int,help='Pause after this many additional decisions')
    args = ap.parse_args()
    require(args.stop_after is None or args.stop_after >= 0,'Negative stop count')
    budget = args.total-2
    folder = args.directory.resolve()
    folder.mkdir(parents=True,exist_ok=True)
    lock = lock_directory(folder,'pairs.py')
    source = HERE/'hexads.cpp'
    hexads = six_rectangles()
    pairs,mass = inventory()
    prefix = ' '.join(map(str,ROWS))+'\n'+''.join(f'{a} {b}\n' for a,b in hexads)
    signature = dict(input_sha256=sha256(prefix.encode()).hexdigest(),
                     inventory_sha256=sha256(json.dumps(pairs,separators=(',',':')).encode()).hexdigest(),
                     solver_sha256=sha256(source.read_bytes()).hexdigest(),hexad_budget=budget)
    journal = folder/'decisions.json'
    if journal.exists():
        record = json.loads(journal.read_text())
        require(record['signature'] == signature,'The saved case inventory or solver differs')
    else:
        record = dict(signature=signature,excluded=[],candidate=None)
        atomic(journal,record)
    excluded = record['excluded']
    require(len(excluded) <= len(pairs) and all(type(n) is int and n>0 for n in excluded),
            'Invalid saved frontier')
    def status(state):
        atomic(folder/'status.json',dict(status=state,observed_utc=datetime.now(timezone.utc).isoformat(),
               pid=os.getpid(),representatives=len(pairs),represented_ordered_pairs=mass,
               excluded=len(excluded),states=sum(excluded),next_case=len(excluded)))
    if record['candidate'] is not None:
        found = record['candidate']
        require(found['case'] == len(excluded) and
                confirmed(pairs[found['case']],found['ids'],hexads,budget) == found['rectangles'],
                'Saved candidate differs')
        status('candidate')
        return
    start = len(excluded)
    stop = len(pairs) if args.stop_after is None else min(len(pairs),start+args.stop_after)
    if stop > start:
        with TemporaryDirectory() as d:
            binary = str(Path(d)/'pair-cover')
            subprocess.run(['c++','-O3','-std=c++20',str(source),'-o',binary],check=True)
            with subprocess.Popen([binary],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as proc:
                try:
                    proc.stdin.write(prefix)
                    for n in range(start,stop):
                        status('running')
                        fill = covered_rows(pair_boxes(pairs[n]))
                        proc.stdin.write(f'{budget} 0 -1 0\n'+' '.join(map(str,fill))+'\n')
                        proc.stdin.flush()
                        line = proc.stdout.readline().split()
                        require(len(line) >= 2 and int(line[1]) > 0,'Missing pair-search result')
                        if line[0] == 'COVER':
                            ids = list(map(int,line[2:]))
                            record['candidate'] = dict(case=n,ids=ids,rectangles=confirmed(pairs[n],ids,hexads,budget))
                            atomic(journal,record)
                            status('candidate')
                            return
                        require(line[0] == 'EXCLUDED' and len(line) == 2,'Unexpected pair-search outcome')
                        excluded.append(int(line[1]))
                        atomic(journal,record)
                finally:
                    proc.stdin.close()
                require(proc.wait() == 0,'Pair-search executable failed')
    status('complete' if len(excluded) == len(pairs) else 'paused')
    print(len(excluded),'of',len(pairs),'representatives excluded,',sum(excluded),'states')


if __name__ == '__main__':
    main()
