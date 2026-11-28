"""Journal the 4,911 five-rectangle orbits at size 14 in independently replayable blocks."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
from math import comb
import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory

from at_fourteen import check
from replay import anchors, program
from input_data import HERE, ROWS, geometry, require
from journal import lock_directory
from pairs import atomic
from rectangles import covered_rows, six_rectangles

BLOCK = 16


def validate(blocks, seeds):
    current = states = mass = 0
    maximum = six_rectangles()
    for row in blocks:
        stop = min(current + BLOCK,len(seeds))
        require(current < stop and all(row[k] == v for k,v in dict(
            start=current,stop=stop,stride=1,tested=stop-current,fixed=5,budget=14,solver='search').items()),
            'A saved block refers to a different range')
        weight = sum(s[-1] for s in seeds[current:stop])
        require(row['physical_fixed_subsets'] == weight and row['search_states'] >= stop-current
                and len(bytes.fromhex(row['all_decisions_sha256'])) == 32, 'Invalid saved block receipt')
        for w in row['covers']:
            boxes = list(map(tuple,w['rectangles']))
            require(current <= w['orbit'] < stop and len(boxes) <= 14 and covered_rows(boxes) == list(ROWS)
                    and boxes[:5] == [maximum[j] for j in seeds[w['orbit']][:-1]], 'Incorrect saved witness')
        current = stop
        states += row['search_states']
        mass += weight
    return current,states,mass


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory',type=Path)
    ap.add_argument('--stop-after',type=int,help='Maximum number of additional 16-orbit blocks')
    args = ap.parse_args()
    require(args.stop_after is None or args.stop_after >= 0,'Negative limit')
    dest = args.directory.resolve()
    dest.mkdir(parents=True,exist_ok=True)
    with lock_directory(dest,'five_at_fourteen.py'), TemporaryDirectory() as scratch:
        d = Path(scratch)
        board, source = d/'board', d/'seeds'
        board.write_text(geometry())
        seeds = anchors(program('anchors',d),board,5,source)
        require(len(seeds) == 4911 and sum(s[-1] for s in seeds) == comb(168,5),'Invalid five-subset inventory')
        signed = ['five_at_fourteen.py','at_fourteen.py','replay.py','search.cpp','coloring.hpp',
                  'cliques.hpp','common.hpp','anchors.cpp','input_data.py']
        signature = dict(block_size=BLOCK,budget=14,fixed=5,board_sha256=sha256(board.read_bytes()).hexdigest(),
                         anchors_sha256=sha256(source.read_bytes()).hexdigest(),
                         source_sha256={n:sha256((HERE/n).read_bytes()).hexdigest() for n in signed})
        path = dest/'journal.json'
        blocks = []
        if path.exists():
            old = json.loads(path.read_bytes())
            require(old['signature'] == signature,'Search inputs changed')
            blocks = old['blocks']
        current,states,mass = validate(blocks,seeds)
        if path.exists():
            require((current,states,mass)==(old['tested'],old['search_states'],old['physical_fixed_subsets']),
                    'Saved totals differ')
        def save(status):
            atomic(path,dict(status=status,observed_utc=datetime.now(timezone.utc).isoformat(),pid=os.getpid(),
                             tested=current,total_orbits=len(seeds),physical_fixed_subsets=mass,search_states=states,
                             signature=signature,blocks=blocks))
        limit = len(seeds) if args.stop_after is None else min(len(seeds),current+BLOCK*args.stop_after)
        if current < limit and not any(row['covers'] for row in blocks):
            binary = program('search',d)
            save('running')
            while current < limit:
                stop = min(len(seeds),current+BLOCK)
                row = check(board,seeds,source,binary,5,current,stop,1)
                blocks.append(row)
                current = stop
                states += row['search_states']
                mass += row['physical_fixed_subsets']
                if row['covers']:
                    break
                save('running')
        found = any(row['covers'] for row in blocks)
        state = 'candidate' if found else ('complete' if current == len(seeds) else 'paused')
        save(state)
        print(state,current,'of',len(seeds),'five-rectangle orbits,',states,'search states')


if __name__ == '__main__':
    main()
