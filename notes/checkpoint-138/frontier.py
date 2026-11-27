"""Resume the size-13 search with any three exceptional maximal rectangles and ten maximum rectangles."""
import argparse
from datetime import datetime,timezone
from hashlib import sha256
from math import comb
import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory

from replay import HERE, PRIOR, bits, build, case, covered_rows, digest, execute, group, inventory, perm_mask, prefix, require, six_rectangles
from rectangles import maximal_rectangles
from triples import area, unpack
from pairs import atomic
from journal import lock_directory


def shape(w):
    return tuple(sorted(x.bit_count() for x in unpack(w)))


def validated(t, ids, boxes):
    require(len(ids)==len(set(ids))<=10 and all(0<=i<len(boxes) for i in ids),'Invalid candidate IDs')
    rects = [unpack(w) for w in t]+[boxes[i] for i in ids]
    from rectangles import ROWS
    require(covered_rows(rects)==list(ROWS),'Candidate fails on the original board')
    return [list(b) for b in rects]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path)
    parser.add_argument('--stop-after',type=int,help='Stop after this many additional first-pair cases')
    parser.add_argument('--jobs',type=int,default=1)
    args = parser.parse_args()
    require(args.jobs>=1 and (args.stop_after is None or args.stop_after>=0),'Invalid job limit')
    dest = args.directory.resolve()
    dest.mkdir(parents=True,exist_ok=True)
    lock = lock_directory(dest,'frontier.py')
    pairs,_ = inventory()
    order = sorted(range(len(pairs)),key=lambda i:(all(area(w)==16 for w in pairs[i][:2]),i))
    boxes = six_rectangles()
    board = prefix(boxes)
    shapes = [tuple(sorted(row['shape'])) for row in json.loads((PRIOR/'results.json').read_text())['geometry']['shape_orbits'] if 'roots' in row]
    members = sorted(a | b<<21 for a,b in maximal_rectangles() if a.bit_count()*b.bit_count()!=36)
    ranks = {w:shapes.index(shape(w)) for w in members}
    record_file = dest/'decisions.json'
    signature = dict(total_budget=13,source_sha256=sha256((HERE/'degree_search.cpp').read_bytes()).hexdigest(),
                     driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),board_sha256=digest(board),
                     inventory_sha256=digest(json.dumps([pairs,order,members],separators=(',',':'))))
    if record_file.exists():
        record = json.loads(record_file.read_text())
        require(record['signature']==signature,'The saved input or program differs')
    else:
        record = dict(signature=signature,excluded=[],candidate=None)
        atomic(record_file,record)
    completed = record['excluded']
    require(len(completed)<=len(order) and all(r['pair_case']==order[k] and r['cases']>0 and r['states']>=0
            and len(r['output_sha256'])==64 for k,r in enumerate(completed)),'Malformed search frontier')
    def status(state):
        atomic(dest/'status.json',dict(observed_utc=datetime.now(timezone.utc).isoformat(),pid=os.getpid(),
               status=state,total_pair_cases=len(order),completed_pairs=len(completed),
               completed_triple_cases=sum(r['cases'] for r in completed),states=sum(r['states'] for r in completed),
               next_pair_case=order[len(completed)] if len(completed)<len(order) else None))
    if record['candidate'] is not None:
        c = record['candidate']
        require(validated(c['words'],c['ids'],boxes)==c['rectangles'],'Saved candidate differs')
        status('candidate')
        return
    end = len(order) if args.stop_after is None else min(len(order),len(completed)+args.stop_after)
    try:
        if len(completed)<end:
            elements = group()
            previous,stabilizer = None,[]
            with TemporaryDirectory() as temp:
                binary = build(HERE/'degree_search.cpp',Path(temp))
                for k in range(len(completed),end):
                    status('running')
                    i = order[k]
                    a,b,pair_size = pairs[i]
                    if a!=previous:
                        labels = list(bits(a))
                        stabilizer = [g for g in elements if all(a>>g[j]&1 for j in labels)]
                        previous = a
                    labels = list(bits(b))
                    maps = [perm_mask(g) for g in stabilizer if all(b>>g[j]&1 for j in labels)]
                    require(len(maps)*pair_size==len(stabilizer),'Pair stabilizer differs')
                    left = {w for w in members if ranks[w]>=ranks[b] and w not in (a,b)}
                    choices,sixths = [],0
                    for w in members:
                        if w not in left:
                            continue
                        orbit = {move(w) for move in maps}
                        require(w in orbit and orbit<=left,'Third-rectangle orbit differs')
                        left -= orbit
                        choices.append(w)
                        distinct = len({ranks[a],ranks[b],ranks[w]})
                        # Six times the contribution to the unmarked unordered triple count.
                        sixths += (1,3,6)[distinct-1]*(len(elements)//len(maps))*len(orbit)
                    require(not left and choices,'Incomplete third-rectangle inventory')
                    inputs = [case(10,0,-1,-1,[],-1,covered_rows([unpack(a),unpack(b),unpack(w)])) for w in choices]
                    outcomes = execute(binary,board,inputs,args.jobs)
                    states,profiles = 0,0
                    for w,row in zip(choices,outcomes):
                        if row[0]=='COVER':
                            ids = list(map(int,row[3:]))
                            record['candidate'] = dict(pair_case=i,words=[a,b,w],ids=ids,rectangles=validated([a,b,w],ids,boxes))
                            atomic(record_file,record)
                            status('candidate')
                            print('Complete cover',record['candidate'],flush=True)
                            return
                        require(len(row)==3 and row[0]=='EXCLUDED','Incomplete binary decision')
                        states += int(row[1])
                        profiles += int(row[2])
                    completed.append(dict(pair_case=i,cases=len(choices),states=states,profiles=profiles,
                        physical_weight_sixths=sixths,input_sha256=digest(board+''.join(inputs)),
                        output_sha256=digest(''.join(' '.join(row)+'\n' for row in outcomes))))
                    atomic(record_file,record)
    except (Exception,KeyboardInterrupt):
        status('interrupted')
        raise
    if len(completed)==len(order):
        require(sum(r['physical_weight_sixths'] for r in completed)==6*comb(len(members),3),
                'The normalized cases do not account for all unordered physical triples')
    status('complete' if len(completed)==len(order) else 'paused')
    print(len(completed),'of',len(order),'pair cases,',sum(r['cases'] for r in completed),'triple cases excluded')
    lock.close()


if __name__=='__main__':
    main()
