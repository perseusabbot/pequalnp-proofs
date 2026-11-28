"""Reproduce the exhaustive coloring searches, the independent hull search, and the clique obstruction."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from contextlib import ExitStack
from hashlib import sha256
from heapq import merge
from math import comb
from pathlib import Path
import json
import subprocess
from tempfile import TemporaryDirectory

from input_data import HERE, ROWS, geometry, require
from rectangles import bits, covered_rows


def program(name, folder):
    dest = folder/name
    subprocess.run(['c++', '-O3', '-march=native', '-std=c++20', str(HERE/(name+'.cpp')), '-o', str(dest)], check=True)
    return dest


def anchors(binary, board, k, out):
    with out.open('w') as stream:
        subprocess.run([binary, board, str(k)], stdout=stream, stderr=subprocess.PIPE, check=True)
    data = [list(map(int, s.split())) for s in out.read_text().splitlines()]
    require(sum(r[-1] for r in data) == comb(168,k) and len({tuple(r[:-1]) for r in data}) == len(data),
            'Fixed families have incorrect orbit mass or repeat')
    return data


def audit(k, mode, paths, seeds):
    digest = sha256(); nodes = cases = edges = triangles = marked = weighted_edges = 0
    worst = None
    with ExitStack() as stack:
        files = [stack.enter_context(p.open()) for p in paths]
        lines = merge(*files, key=lambda line: int(line.split()[0 if mode=='obstructions' else 1]))
        for i, line in enumerate(lines):
            words = line.split(); digest.update(line.encode())
            require(i < len(seeds), 'Unexpected result')
            if mode == 'obstructions':
                z, mass, e, t, q, stamp = map(int, words)
                require(z == i and mass == seeds[i][-1] and 0 <= q <= t and 0 <= e <= comb(162,2)
                        and 0 <= stamp < 2**64, 'Malformed obstruction result')
                edges += e; triangles += t; marked += q; weighted_edges += e*mass
            else:
                require(words[0]=='EXCLUDED', 'A possible cover needs separate verification: '+line)
                fields = list(map(int, words[1:]))
                if mode == 'hulls': z, holes, states = fields
                else:
                    z, mass, holes, states = fields
                    require(mass == seeds[i][-1], 'Wrong orbit multiplicity')
                require(i == z and 336-36*k <= holes <= 336 and states > 0, 'Invalid coloring result')
                nodes += states
                if worst is None or states > worst['states']: worst = dict(orbit=i, states=states)
            cases += 1
    require(cases == len(seeds), 'A fixed family is missing')
    result = dict(representatives=cases, fixed=k, physical_fixed_families=comb(168,k),
                  canonical_output_sha256=digest.hexdigest())
    if mode == 'obstructions':
        require(weighted_edges % comb(8,6) == 0, 'Wrong marked-pair mass')
        result.update(marked_pairs=edges, marked_triangles=triangles, nine_markings_checked=marked,
                      physical_eight_families_without_six_clique=weighted_edges//comb(8,6),
                      all_eight_families=comb(168,8), all_nine_families=comb(168,9))
    else: result.update(remaining_colors=13-k, search_nodes=nodes, largest_search=worst)
    return result


def check_controls(binary, board):
    fifteen = json.loads((HERE.parent/'checkpoint-134/board.json').read_text())['published_fifteen']
    require(covered_rows(fifteen) == list(ROWS), 'The published size-15 example differs')
    seven = [(0,1),(1,2),(2,12),(5,6),(6,7),(7,0),(16,5)]
    known = []
    for k in (4,5,6,7):
        for count in ([k,k+1] if k<7 else [k]):
            r = [0]*21
            for p,q in seven[:count]: r[p] |= 1<<q
            known.append((k,r,count<=k))
    for k in (4,5,6,7,8,9):
        fill = covered_rows(fifteen[:-k])
        known.append((k,[r & ~f for r,f in zip(ROWS,fill)],True))
    known.append((4,[0]*21,True))
    script = ''.join(' '.join(map(str,[k,*r]))+'\n' for k,r,_ in known)
    raw = subprocess.check_output([binary,board],input=script,text=True).splitlines()
    require(len(raw)==len(known),'A control was omitted')
    report = []
    for s,(k,required,yes) in zip(raw,known):
        verdict,states,*fields=s.split()
        require(verdict==('COVER' if yes else 'EXCLUDED'),'Wrong control result')
        if yes:
            values=list(map(int,fields));require(len(values)==2*k,'Malformed cover')
            boxes = list(zip(values[::2],values[1::2])); actual = covered_rows(boxes)
            require(all(not(a&~b) for a,b in zip(required,actual)), 'Control misses a required zero')
        report.append(dict(colors=k,required=sum(r.bit_count() for r in required),cover=yes,states=int(states)))
    return report


def compute(mode, folder, jobs):
    board=folder/'board';board.write_text(geometry())
    if mode=='controls':return check_controls(program('controls',folder),board)
    k=6 if mode=='obstructions' else (4 if mode=='hulls' else int(mode))
    path=folder/'seeds';seeds=anchors(program('anchors',folder),board,k,path)
    binary=program('obstructions' if mode=='obstructions' else ('hulls' if mode=='hulls' else 'search'),folder)
    def worker(i):
        output=folder/f'result-{i}'
        args=[binary,board,path]
        if mode!='obstructions': args.append(str(k))
        if mode not in ('hulls','obstructions'):args.append(str(13-k))
        with output.open('w') as stream:subprocess.run([*args,str(i),str(len(seeds)),str(jobs)],stdout=stream,check=True)
        return output
    with ThreadPoolExecutor(max_workers=jobs) as pool:files=list(pool.map(worker,range(jobs)))
    result=audit(k,mode,files,seeds);result['anchors_sha256']=sha256(path.read_bytes()).hexdigest()
    return result


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode',choices=['4','5','6','hulls','obstructions','controls'])
    ap.add_argument('--jobs',type=int,default=1);ap.add_argument('--output',type=Path)
    args=ap.parse_args();require(args.jobs>0,'Invalid worker count')
    with TemporaryDirectory() as d:report=compute(args.mode,Path(d),args.jobs)
    if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')
    else:require(json.loads((HERE/'results.json').read_text())[args.mode]==report,'Published computation differs')
    print(args.mode,'verified')
