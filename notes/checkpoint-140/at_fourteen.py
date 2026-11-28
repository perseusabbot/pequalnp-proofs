"""Test size-14 completions with five or six fixed maximum rectangles."""
import argparse
from hashlib import sha256
import json
from math import comb
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from replay import anchors, program
from input_data import ROWS, geometry, require
from rectangles import covered_rows, six_rectangles


def check(board, seeds, source, binary, fixed, start, stop, stride):
    maximum = six_rectangles()
    ids = range(start, stop, stride)
    color = binary.name == 'search'
    args = ([binary, board, source, fixed, 14-fixed, start, stop, stride] if color
            else [binary, board, source, fixed, start, stop, stride, 14])
    digest = sha256()
    states = mass = count = 0
    witnesses = []
    with subprocess.Popen(list(map(str,args)), stdout=subprocess.PIPE) as child:
        for raw in child.stdout:
            require(count < len(ids), 'A solver returned too many cases')
            digest.update(raw)
            kind, *fields = raw.decode().split()
            values = list(map(int,fields))
            idx = ids[count]
            require(values[0] == idx, 'Unexpected orbit index')
            orbit = seeds[idx]
            base = [maximum[k] for k in orbit[:-1]]
            base_cover = covered_rows(base)
            holes = sum((r & ~v).bit_count() for r,v in zip(ROWS,base_cover))
            if color:
                require(values[1] == orbit[-1] and values[2] == holes and values[3] >= 1,
                        'Invalid color-search receipt')
                states += values[3]
            if kind == 'EXCLUDED':
                if color:
                    require(len(values) == 4, 'Invalid color-search exclusion')
                else:
                    require(len(values) == 3 and values[1] == holes and values[2] >= 1,
                            'Invalid hull-search exclusion')
                    states += values[2]
            else:
                require(kind == 'COVER', 'Unrecognized search result')
                coords = values[5:] if color else values[1:]
                require(len(coords) % 2 == 0, 'Truncated rectangle list')
                boxes = list(zip(coords[::2],coords[1::2]))
                if color:
                    require(values[4] == len(boxes) and boxes[:fixed] == base, 'Fixed rectangles differ')
                else:
                    require(len(boxes) == 14-fixed, 'Short hull witness')
                    boxes = base + [r for r in boxes if all(r)]
                require(len(boxes) <= 14 and covered_rows(boxes) == list(ROWS), 'Invalid positive witness')
                witnesses.append(dict(orbit=idx,rectangles=boxes))
            mass += orbit[-1]
            count += 1
        require(child.wait() == 0 and count == len(ids), 'Incomplete search range')
    return dict(fixed=fixed,budget=14,solver=binary.name,start=start,stop=stop,stride=stride,
                tested=count,physical_fixed_subsets=mass,search_states=states,
                all_decisions_sha256=digest.hexdigest(),covers=witnesses)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fixed',type=int,choices=[5,6],required=True)
    ap.add_argument('--solver',choices=['search','hulls'],required=True)
    ap.add_argument('--start',type=int,default=0)
    ap.add_argument('--stop',type=int)
    ap.add_argument('--stride',type=int,default=1)
    ap.add_argument('--output',type=Path)
    a = ap.parse_args()
    with TemporaryDirectory() as folder:
        d = Path(folder)
        board, source = d/'board', d/'seeds'
        board.write_text(geometry())
        roots = anchors(program('anchors',d),board,a.fixed,source)
        stop = len(roots) if a.stop is None else a.stop
        require(0 <= a.start <= stop <= len(roots) and a.stride > 0, 'Invalid range')
        report = check(board,roots,source,program(a.solver,d),a.fixed,a.start,stop,a.stride)
        if a.start == 0 and a.stride == 1 and stop == len(roots):
            require(report['physical_fixed_subsets'] == comb(168,a.fixed),'The full orbit mass differs')
    raw = json.dumps(report,indent=2) + '\n'
    if a.output:
        a.output.write_text(raw)
    print(raw,end='')
