"""Resume the size-13 search allowing four exceptional maximal rectangles of area at least 24."""
import argparse
from datetime import datetime,timezone
from hashlib import sha256
from math import comb
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from inventory import HERE, build_input, inventory, json, require
from pairs import atomic, pair_boxes
from journal import lock_directory
from rectangles import ROWS, covered_rows, maximal_rectangles, six_rectangles


def candidate(words, pair, members, maximum):
    a,b,c,d,*hs=map(int,words)
    require(all(0<=j<len(members) for j in (a,b,c,d)) and len({a,b,c,d})==4,'Invalid exceptional indices')
    require({members[a],members[b]}==set(pair_boxes(pair)),'Marked pair differs')
    require(len(hs)==len(set(hs))==9 and all(0<=j<168 for j in hs),'Invalid maximum rectangles')
    boxes=[members[j] for j in (a,b,c,d)]+[maximum[j] for j in hs]
    require(covered_rows(boxes)==list(ROWS),'Candidate fails on the posted board')
    return [list(x) for x in boxes]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory',type=Path)
    ap.add_argument('--stop-after',type=int,help='Maximum number of new marked pairs to finish in this run')
    args=ap.parse_args()
    require(args.stop_after is None or args.stop_after>=0,'Invalid stop limit')
    folder=args.directory.resolve()
    folder.mkdir(exist_ok=True,parents=True)
    lock=lock_directory(folder,'large.py')
    data=build_input()
    pairs,_=inventory()
    order=[i for i,p in enumerate(pairs) if all(a.bit_count()*b.bit_count()>16 for a,b in pair_boxes(p))]
    members=[(a,b) for _,a,b in sorted((a|b<<21,a,b) for a,b in maximal_rectangles() if a.bit_count()*b.bit_count()!=36)]
    maximum=six_rectangles()
    signature=dict(input_sha256=sha256(data.encode()).hexdigest(),budget=13,
        source_sha256={n:sha256((HERE/n).read_bytes()).hexdigest() for n in
                       ['board.hpp','profiles.hpp','complete.hpp','scan.cpp','large.py']})
    file=folder/'decisions.json'
    if file.exists():
        record=json.loads(file.read_text())
        require(record['signature']==signature,'Saved geometry or solver differs')
    else:
        record=dict(signature=signature,excluded=[],candidate=None)
        atomic(file,record)
    completed=record['excluded']
    require(len(completed)<=len(order) and all(r[0]==order[j] and len(r)==12 and
            r[1]==sum(r[5:10]) and r[2]>0 for j,r in enumerate(completed)),'Invalid saved frontier')
    def status(state):
        atomic(folder/'status.json',dict(status=state,observed_utc=datetime.now(timezone.utc).isoformat(),
               pid=os.getpid(),completed_pairs=len(completed),total_pairs=len(order),
               representative_quadruples=sum(r[1] for r in completed),
               search_states=sum(r[-1] for r in completed),
               next_pair=order[len(completed)] if len(completed)<len(order) else None))
    if record['candidate']:
        c=record['candidate']
        require(candidate(c['indices'],pairs[c['pair']],members,maximum)==c['rectangles'],'Saved cover differs')
        status('candidate')
        return
    end=len(order) if args.stop_after is None else min(len(order),len(completed)+args.stop_after)
    try:
        if len(completed)<end:
            with TemporaryDirectory() as tmp:
                tmp=Path(tmp)
                (tmp/'inventory').write_text(data)
                solver=tmp/'scan'
                subprocess.run(['c++','-O3','-std=c++20',str(HERE/'scan.cpp'),'-o',str(solver)],check=True)
                status('running')
                command=[str(solver),str(tmp/'inventory'),'9',str(order[len(completed)]),str(order[end-1]+1),'1','four-large']
                with subprocess.Popen(command,stdout=subprocess.PIPE,text=True) as proc:
                    for line in proc.stdout:
                        kind,*fields=line.split()
                        values=list(map(int,fields))
                        i=values[0]
                        require(len(completed)<end and i==order[len(completed)],'Incomplete or reordered search')
                        if kind=='COVER4':
                            result=candidate(values[1:],pairs[i],members,maximum)
                            record['candidate']=dict(pair=i,indices=values[1:],rectangles=result)
                            atomic(file,record)
                            status('candidate')
                            print('Complete 13-rectangle cover',result,flush=True)
                            return
                        require(kind=='LARGE' and len(values)==12 and values[1]==sum(values[5:10]),'Invalid pair result')
                        completed.append(values)
                        atomic(file,record)
                        status('running')
                    require(proc.wait()==0 and len(completed)==end,'Search stopped before its last root')
    except (Exception,KeyboardInterrupt):
        status('interrupted')
        raise
    if len(completed)==len(order):
        require(sum(r[2] for r in completed)==24*comb(24920,4),'The marked pairs have the wrong physical mass')
    status('complete' if len(completed)==len(order) else 'paused')
    print(len(completed),'of',len(order),'pair roots,',sum(r[1] for r in completed),'quadruples excluded')
    lock.close()


if __name__=='__main__':
    main()
