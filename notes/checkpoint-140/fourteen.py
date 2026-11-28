"""Resume the size-14 search with six marked maximum rectangles and eight arbitrary rectangles."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from replay import anchors, program
from input_data import HERE, ROWS, geometry, require
from journal import lock_directory
from pairs import atomic
from rectangles import covered_rows, six_rectangles

BLOCK=64


def parsed(line,index,seeds,maximum):
    kind,*fields=line.split();values=list(map(int,fields))
    require(len(values)>=4 and values[0]==index and values[1]==seeds[index][-1] and values[3]>0,'Invalid case receipt')
    fill=covered_rows([maximum[j] for j in seeds[index][:-1]])
    require(values[2]==sum((r&~f).bit_count() for r,f in zip(ROWS,fill)),'Incorrect residual size')
    if kind=='EXCLUDED':
        require(len(values)==4,'Trailing fields in exclusion')
        return values[3],None
    require(kind=='COVER' and len(values)>=5,'Unsupported verdict')
    n=values[4];coords=values[5:]
    require(6<=n<=14 and len(coords)==2*n,'Wrong size-14 candidate length')
    boxes=list(zip(coords[::2],coords[1::2]))
    require(boxes[:6]==[maximum[j] for j in seeds[index][:-1]] and covered_rows(boxes)==list(ROWS),
            'Candidate fails on the original matrix')
    return values[3],[list(b) for b in boxes]


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('directory',type=Path)
    ap.add_argument('--stop-after',type=int,help='Number of new blocks of 64 orbits to finish')
    args=ap.parse_args();require(args.stop_after is None or args.stop_after>=0,'Negative stop limit')
    dest=args.directory.resolve();blocks=dest/'blocks';blocks.mkdir(exist_ok=True,parents=True)
    with lock_directory(dest,'fourteen.py'),TemporaryDirectory() as tmp:
        tmp=Path(tmp);board=tmp/'board';board.write_text(geometry());src=dest/'anchors.txt'
        if not src.exists():
            built=tmp/'six';anchors(program('anchors',tmp),board,6,built)
            stage=src.with_suffix('.tmp');stage.write_bytes(built.read_bytes());stage.replace(src)
        seeds=[list(map(int,s.split())) for s in src.read_text().splitlines()]
        require(len(seeds)==121572 and sum(s[-1] for s in seeds)==28530983404,'Invalid six-subset inventory')
        signature=dict(budget=14,block_size=BLOCK,board_sha256=sha256(board.read_bytes()).hexdigest(),
                       anchors_sha256=sha256(src.read_bytes()).hexdigest(),
                       source_sha256={n:sha256((HERE/n).read_bytes()).hexdigest() for n in
                                      ['fourteen.py','search.cpp','common.hpp','cliques.hpp','coloring.hpp','anchors.cpp','input_data.py']})
        if (dest/'signature.json').exists():require(json.loads((dest/'signature.json').read_bytes())==signature,'Input or solver changed')
        else:atomic(dest/'signature.json',signature)
        current=states=mass=number=0;maximum=six_rectangles()
        for p in sorted(blocks.glob('*.tsv')):
            require(p.name==f'{number:05}.tsv','Search blocks are not contiguous')
            lines=p.read_text().splitlines();require(len(lines)==min(BLOCK,len(seeds)-current),'Incomplete saved block')
            for line in lines:
                nodes,candidate=parsed(line,current,seeds,maximum);require(candidate is None,'Unexpected embedded cover')
                states+=nodes;mass+=seeds[current][-1];current+=1
            number+=1
        def status(state):
            atomic(dest/'status.json',dict(status=state,observed_utc=datetime.now(timezone.utc).isoformat(),pid=os.getpid(),
                                          completed_blocks=number,excluded=current,total_orbits=len(seeds),
                                          physical_six_subsets_excluded=mass,search_states=states))
        witness=dest/'candidate.json'
        if witness.exists():
            c=json.loads(witness.read_bytes());idx=c['orbit']
            require(parsed(c['line'],idx,seeds,maximum)[1]==c['rectangles'],'Saved candidate differs')
            status('candidate');return
        stop=len(seeds) if args.stop_after is None else min(len(seeds),current+BLOCK*args.stop_after)
        if current<stop:
            solver=program('search',tmp);status('running')
            with subprocess.Popen([solver,board,src,'6','8',str(current),str(stop),'1'],stdout=subprocess.PIPE,text=True) as proc:
                try:
                    pending=[];pending_states=0;pending_mass=0
                    for line in proc.stdout:
                        idx=current+len(pending)
                        n,found=parsed(line,idx,seeds,maximum)
                        if found:
                            atomic(witness,dict(orbit=idx,line=line.strip(),rectangles=found))
                            status('candidate');proc.terminate();print('Validated 14-rectangle cover',found,flush=True);return
                        pending.append(line);pending_states+=n;pending_mass+=seeds[idx][-1]
                        if len(pending)==BLOCK or current+len(pending)==len(seeds):
                            out=blocks/f'{number:05}.tsv';tmpout=out.with_suffix('.tmp')
                            tmpout.write_text(''.join(pending));tmpout.replace(out)
                            current+=len(pending);states+=pending_states;mass+=pending_mass;number+=1
                            pending=[];pending_states=pending_mass=0;status('running')
                    require(proc.wait()==0 and not pending and current==stop,'Search ended inside a block')
                except (Exception,KeyboardInterrupt):
                    if proc.poll() is None:proc.terminate()
                    status('interrupted');raise
        status('complete' if current==len(seeds) else 'paused')
        print(current,'of',len(seeds),'orbits excluded,',mass,'physical six-subsets')


if __name__=='__main__':main()
