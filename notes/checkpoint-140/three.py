"""Verify the additional three-rectangle search or regenerate all twenty decisions."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from replay import anchors, audit, compute, program
from input_data import HERE, ROWS, geometry, require
from rectangles import covered_rows, six_rectangles

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--replay', action='store_true', help='Regenerate every ten-color search')
    ap.add_argument('--jobs', type=int, default=1)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    require(args.jobs > 0, 'At least one worker is required')
    with TemporaryDirectory() as folder:
        d = Path(folder)
        if args.replay:
            result = compute('3', d, args.jobs)
        else:
            board, source = d/'board', d/'seeds'
            board.write_text(geometry())
            seeds = anchors(program('anchors',d),board,3,source)
            table = HERE/'three.tsv'
            result = audit(3,'3',[table],seeds)
            result['anchors_sha256'] = sha256(source.read_bytes()).hexdigest()
            maximum = six_rectangles()
            for line,s in zip(table.read_text().splitlines(),seeds,strict=True):
                cells = covered_rows([maximum[i] for i in s[:-1]])
                require(int(line.split()[3]) == sum((r&~v).bit_count() for r,v in zip(ROWS,cells)),
                        'The three-rectangle residual differs')
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads((HERE/'three.json').read_bytes()), 'Three-rectangle receipts differ')
    print(result['representatives'],'three-rectangle orbits,',result['search_nodes'],'search states')
