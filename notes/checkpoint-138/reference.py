"""Independently replay a saved subset of the pair decisions using the previous search algorithm."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from replay import HERE, PRIOR, build, covered_rows, excluded, execute, inventory, line, pair_boxes, prefix, require, six_rectangles


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs',type=int,default=1)
    parser.add_argument('--sample',action='store_true',help='Replay one case for each of the eight first-rectangle shapes')
    args = parser.parse_args()
    require(args.jobs>=1,'At least one worker is required')
    saved = json.loads((HERE/'reference.json').read_text())
    require(sha256((PRIOR/'hexads.cpp').read_bytes()).hexdigest()==saved['solver_sha256'],
            'Independent reference solver differs')
    pairs,_ = inventory()
    ids = saved['sample'] if args.sample else [i for i,n in saved['decisions']]
    expected = dict(saved['decisions'])
    require(len({pairs[k][0] for k in saved['sample']})==8,'The sample misses a shape')
    required = {i for i,p in enumerate(pairs) if i<208 or
                any(a.bit_count()==b.bit_count()==4 for a,b in pair_boxes(p))}
    require(required==set(expected),'The independent reference inventory differs')
    inputs = [line([12,0,-1,0])+line(covered_rows(pair_boxes(pairs[i]))) for i in ids]
    with TemporaryDirectory() as temp:
        binary = build(PRIOR/'hexads.cpp',Path(temp))
        out = excluded(execute(binary,prefix(six_rectangles()),inputs,args.jobs),1)
    require([n for n, in out]==[expected[i] for i in ids],'Independent state counts differ')
    print(len(ids),'pair cases excluded by the earlier independent algorithm;',sum(expected[i] for i in ids),'states')
