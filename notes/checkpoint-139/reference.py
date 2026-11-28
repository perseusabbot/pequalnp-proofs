"""Replay every size-13 residual surviving the local, domination and parity screens with the previous solver."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from inventory import HERE, inventory, maximal_rectangles, prefix, require, six_rectangles
from pairs import pair_boxes
from rectangles import covered_rows


def run(core, jobs, sample_stride=139, folder=None):
    roots,_ = inventory()
    boards=six_rectangles()
    board=prefix(boards)
    members=sorted((a|b<<21,a,b) for a,b in maximal_rectangles() if a.bit_count()*b.bit_count()!=36)
    rows=[tuple(map(int,line.split())) for line in core.read_text().splitlines()]
    require(rows==sorted(set(rows)),'Residuals are repeated or unordered')
    require(all(0<=i<len(roots) and 0<=k<len(members) and q>=0 for i,k,q in rows),'Invalid residual entry')
    previous=HERE.parent/'checkpoint-138/degree_search.cpp'
    independent=HERE.parent/'checkpoint-137/hexads.cpp'
    def group_run(path, kind, subset):
        src=previous if kind=='degree' else independent
        binary=path/(kind+'-solver')
        subprocess.run(['c++','-O3','-std=c++20',str(src),'-o',str(binary)],check=True)
        def work(worker):
            input_file=path/f'{kind}-{worker}.in'
            output_file=path/f'{kind}-{worker}.out'
            chunk=subset[worker::jobs]
            with input_file.open('w') as inp:
                inp.write(board)
                for i,k,q in chunk:
                    _,a,b=members[k]
                    fill=covered_rows([*pair_boxes(roots[i]),(a,b)])
                    inp.write(('10 0 -1 -1 0 -1\n' if kind=='degree' else '10 0 -1 0\n')+' '.join(map(str,fill))+'\n')
            with input_file.open() as inp,output_file.open('w') as out:
                subprocess.run([binary],stdin=inp,stdout=out,check=True)
            lines=output_file.read_text().splitlines()
            require(len(lines)==len(chunk),'Independent output truncated')
            result=[]
            for num,(row,(_,_,expect)) in enumerate(zip(lines,chunk)):
                fields=row.split()
                require(fields[0]=='EXCLUDED' and len(fields)==(3 if kind=='degree' else 2),
                        f'Independent result for {chunk[num]}: {row}')
                if kind=='degree':
                    require(int(fields[2])==expect,'Independent profile count differs')
                result.append((worker+num*jobs,int(fields[1])))
            return result
        with ThreadPoolExecutor(max_workers=jobs) as tasks:
            answers=sorted(item for batch in tasks.map(work,range(jobs)) for item in batch)
        return dict(solver_sha256=sha256(src.read_bytes()).hexdigest(),excluded=len(answers),
                    states=sum(s for _,s in answers),
                    output_sha256=sha256(''.join(str(s)+'\n' for _,s in answers).encode()).hexdigest())
    with TemporaryDirectory(dir=folder) as temp:
        d=Path(temp)
        degree=group_run(d,'degree',rows)
        independent_result=group_run(d,'independent',rows[::sample_stride])
    return dict(core_sha256=sha256(core.read_bytes()).hexdigest(),degree_search=degree,
                independent_stride=sample_stride,previous_degree_free_search=independent_result)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('residuals',type=Path)
    ap.add_argument('--jobs',type=int,default=1)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    require(args.jobs>0,'At least one worker is needed')
    result=run(args.residuals,args.jobs)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    else:require(result==json.loads((HERE/'reference.json').read_text()),'Independent receipt differs')
    print(result['degree_search']['excluded'],'degree-profile replays,',result['previous_degree_free_search']['excluded'],'degree-free replays')
