"""Rebuild the unrestricted eight-replacement instance from the earlier witness."""
import argparse
import hashlib
import json
from math import comb
import os
from pathlib import Path
import subprocess
import tempfile

from verify import HERE, ROWS, require


def instance(radius):
    previous=HERE.parent/'checkpoint-133'
    data=json.loads((previous/'plane-examples.json').read_text())['unrestricted']
    boxes=data['rectangles']
    occupied=[sum(1<<j for j in range(21) if any(a>>i & b>>j & 1 for a,b in boxes)) for i in range(21)]
    require(len(boxes)==14 and len(set(map(tuple,boxes)))==14, 'Incumbent inventory')
    require(all(not got & ~row for got,row in zip(occupied,ROWS)), 'Incumbent at forbidden entry')
    require(sum(r.bit_count() for r in occupied)==334, 'Incumbent area')
    require([(i,j) for i in range(21) for j in range(21) if (ROWS[i]^occupied[i])>>j&1]==[(6,18),(13,10)],
            'Uncovered entries differ')
    return ('\n'.join([f'21 14 {radius}', ' '.join(map(str,ROWS)), *(f'{a} {b}' for a,b in boxes)])+'\n').encode()


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write-input',type=Path,help='Save a standalone C++ solver input')
    ap.add_argument('--radius',type=int,choices=(8,9),default=8)
    ap.add_argument('--solve',action='store_true',help='Compile and run the complete coloring search')
    args=ap.parse_args()
    payload=instance(args.radius)
    previous=HERE.parent/'checkpoint-133'
    expected={8:'eeb792e705901530ae439f70e6fa103a78cd1edf7b9306e057f7dcc1edaeccc5',
              9:'e7185477db832d5d84b011ed505c2c748d2f7d667ef17df1c33af257ab90450c'}
    digest=hashlib.sha256(payload).hexdigest()
    require(digest==expected[args.radius], 'Input differs from Checkpoint 133')
    if args.write_input:
        args.write_input.write_bytes(payload)
    if args.solve:
        with tempfile.TemporaryDirectory() as tmp:
            binary=Path(tmp)/'repair'
            subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(previous/'repair.cpp'),'-o',str(binary)],check=True)
            result=subprocess.check_output([str(binary)],input=payload).decode().strip()
        if args.radius==8:
            require(result==f'EXCLUDED 8 {comb(14,8)} 337987474 1939485', 'Radius-eight replay differs')
        print(result)
    print('sha256',digest)


if __name__=='__main__':
    main()
