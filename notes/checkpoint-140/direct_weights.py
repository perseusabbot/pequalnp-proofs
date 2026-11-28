"""Replay the weight trees using a second rectangle enumeration and an independent integer checker."""
import argparse
import gzip
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory
from replay import program
from input_data import HERE, group, require


def write_node(out, node):
    print(*node['w'], file=out)
    children = node.get('children', [])
    print(len(children), file=out)
    for e, child in children:
        print(e, file=out)
        write_node(out, child)


def compute(matrix, names):
    raw = matrix.read_bytes()
    match = re.search(rb'^def incidence : List Nat := \[([0-9, ]+)\]$', raw, re.M)
    require(match is not None and sha256(raw).hexdigest() ==
            'd036a648649d11adbb25b8ed6d9e7ac34d1edd24e56b14e8891e6408502a093a', 'Wrong board')
    rows = [((1<<21)-1)^int(v) for v in match.group(1).split(b',')]
    with TemporaryDirectory() as folder:
        tmp = Path(folder); board = tmp/'geometry'; stream = tmp/'certificates'
        with board.open('w') as f:
            print(*rows, file=f); gens=group()[1:6]; print(len(gens),file=f)
            for g in gens: print(*g,file=f)
        with stream.open('w') as f:
            print(len(names),file=f)
            for name in names:
                obj = json.loads(gzip.decompress((HERE/'certificates'/(name+'.json.gz')).read_bytes()))
                print(obj['fixed_maximum_count'],obj['exceptional_area_cap'],len(obj['cases']),file=f)
                for case in obj['cases']:
                    print(*case['maximum'],file=f)
                    write_node(f,case['proof'])
        output=subprocess.check_output([program('direct_weights',tmp),board,stream],text=True)
    lines=output.splitlines()
    require(len(lines)==len(names),'A certificate stratum was omitted')
    fields=['fixed','exceptional_area_cap','root_orbits','physical_roots','nodes','leaves','splits','deepest_mark']
    answer={name:dict(zip(fields,map(int,s.split()),strict=True)) for name,s in zip(names,lines)}
    return answer


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('matrix',type=Path)
    ap.add_argument('strata',nargs='+')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();data=compute(args.matrix,args.strata)
    if args.output:args.output.write_text(json.dumps(data,indent=2)+'\n')
    else:
        published=json.loads((HERE/'direct.json').read_bytes())
        require(data=={n:published[n] for n in args.strata},'Direct certificate replay differs')
    print(sum(v['nodes'] for v in data.values()),'integer certificates checked directly')
