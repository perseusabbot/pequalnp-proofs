"""Resume independent coloring searches on symmetry representatives of the incumbent subsets."""
import argparse
from datetime import datetime,timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile

from journal import lock_directory
from plane import HERE, ROWS, bits, group, require
from repairs import SEED, anchors, instance, maps_on_seed

MODES={'full-nine':(9,0),'near-eight':(8,1),'near-nine':(9,1)}


def atomic(path,value):
    temp=path.with_suffix('.tmp')
    temp.write_text(json.dumps(value,separators=(',',':'))+'\n')
    temp.replace(path)


def checked_candidate(lines,mask,board,seed,allowed):
    boxes=[tuple(map(int,line.split())) for line in lines]
    require(len(boxes)==14 and all(len(b)==2 for b in boxes),'Incomplete rectangle witness')
    kept=[tuple(seed[i]) for i in bits(mask)]
    require(boxes[:len(kept)]==kept,'Retained rectangles changed')
    occupied=[0]*21
    for a,b in boxes:
        require(0<=a<1<<21 and 0<=b<1<<21,'Rectangle coordinates out of range')
        for p in bits(a):occupied[p]|=b
    require(all(w&~r==0 for w,r in zip(occupied,board)),'Witness covers a forbidden entry')
    missing=[(p,l) for p,w in enumerate(board) for l in bits(w&~occupied[p])]
    require(len(missing)<=allowed,'Witness misses too many zeros')
    return dict(rectangles=boxes,missing=missing)


def controls(binary):
    zero=[[0,0]]*14
    keep=(1<<12)-1
    for diagonal,hole,expected in [(2,0,'COVER'),(3,0,'EXCLUDED'),(3,1,'COVER'),(4,1,'EXCLUDED')]:
        board=[(1<<i) if i<diagonal else 0 for i in range(21)]
        data='21 14 2\n'+' '.join(map(str,board))+'\n'+'0 0\n'*14+f'{keep} {hole}\n'
        lines=subprocess.check_output([binary],input=data,text=True).splitlines()
        require(lines[0].split()[0]==expected,'Coloring control failed')
        if expected=='COVER':checked_candidate(lines[1:],keep,board,zero,hole)


def covered(mask):
    selected=[SEED[i] for i in bits(mask)]
    total=0
    for p in range(21):
        row=0
        for a,b in selected:
            if a>>p&1:row|=b
        total+=row.bit_count()
    return total


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode',choices=MODES)
    ap.add_argument('directory',type=Path)
    ap.add_argument('--stop-after',type=int,help='Save progress after this many additional decisions')
    args=ap.parse_args()
    folder=args.directory.resolve()
    folder.mkdir(parents=True,exist_ok=True)
    lock=lock_directory(folder,'windows.py')
    if args.stop_after is not None and args.stop_after<0:raise ValueError('Negative stop count')
    radius,hole=MODES[args.mode]; data=instance(radius)
    elements=group()
    reps,summary=anchors(elements,maps_on_seed(elements),14-radius)
    if args.mode=='near-nine':reps.sort(key=lambda m:(-covered(m),m))
    source=HERE/'window.cpp'
    signature=dict(mode=args.mode,source_sha256=sha256(source.read_bytes()).hexdigest(),input_sha256=sha256(data).hexdigest())
    journal=folder/'decisions.json'
    if journal.exists():
        record=json.loads(journal.read_text())
        require(record['signature']==signature,'Source or input differs from saved results')
        require(set(record['excluded'])<={str(r) for r in reps},'Saved decisions include an unknown representative')
        if record['candidate']:
            c=record['candidate'];checked_candidate([' '.join(map(str,b)) for b in c['rectangles']],c['retained'],ROWS,SEED,hole)
    else:
        record=dict(signature=signature,excluded={},candidate=None)
        atomic(journal,record)
    def status(key=None):
        observed=datetime.now(timezone.utc).isoformat()
        complete=len(record['excluded'])==len(reps)
        state='candidate' if record['candidate'] else 'complete' if complete else 'running' if key is not None else 'paused'
        atomic(folder/'status.json',dict(**signature,observed_utc=observed,pid=os.getpid(),status=state,
              representatives=len(reps),original_subsets=summary['seed_subsets'],excluded=len(record['excluded']),
              states=sum(record['excluded'].values()),current_retained=key))
    if record['candidate'] or len(record['excluded'])==len(reps):status();return
    with tempfile.TemporaryDirectory() as tmp:
        binary=Path(tmp)/'window'
        subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(source),'-o',str(binary)],check=True)
        controls(binary)
        completed=0
        for mask in reps:
            if str(mask) in record['excluded']:continue
            if args.stop_after is not None and completed==args.stop_after:break
            status(mask)
            raw=subprocess.check_output([binary],input=data+f'{mask} {hole}\n'.encode()).decode().splitlines()
            answer,key,states=raw[0].split()
            require(int(key)==mask and int(states)>=0,'Incorrect solver receipt')
            if answer=='COVER':
                record['candidate']=dict(retained=mask,**checked_candidate(raw[1:],mask,ROWS,SEED,hole))
            else:
                require(answer=='EXCLUDED' and len(raw)==1,'Unrecognized coloring result')
                record['excluded'][str(mask)]=int(states)
            atomic(journal,record);completed+=1
            if record['candidate']:break
    status()


if __name__=='__main__':main()
