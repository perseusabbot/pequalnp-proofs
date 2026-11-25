"""Reconstruct the rotation certificate and inventory for the 21 by 21 board."""
import argparse
from collections import Counter
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
N=21
ALL=(1<<N)-1
LINES=[1179809,262467,524934,1049868,2585,5170,10340,20680,41360,82720,165440,330880,661760,1323520,549889,1099778,102405,204810,409620,819240,1638480]
ROWS=[ALL^r for r in LINES]
COLS=[sum(((r>>j)&1)<<i for i,r in enumerate(ROWS)) for j in range(N)]
CELLS=[(i,j) for i in range(3) for j in range(N) if ROWS[i]>>j&1]
PHASES=[tuple(((i+3*q)%21,(j+3*q)%21) for q in range(7)) for i,j in CELLS]
FREE=(0,0,ALL,ALL)

def check(ok, message):
    if not ok:
        raise ValueError(message)


def rotates(word, phase):
    shift = 3 * phase
    return ((word << shift) | (word >> (N - shift))) & ALL


def choices(box, cell_orbit):
    _, _, allowed_rows, allowed_columns = box
    return [phase for phase, (i,j) in enumerate(cell_orbit)
            if (allowed_rows >> i) & (allowed_columns >> j) & 1]


def witness(box, cell_orbit):
    rows, columns = box[:2]
    return any((rows >> i) & (columns >> j) & 1 for i,j in cell_orbit)


def extend(box, i, j):
    rows, columns, allowed_rows, allowed_columns = box
    return (rows | (1 << i), columns | (1 << j),
            allowed_rows & COLS[j], allowed_columns & ROWS[i])


def certificate():
    entries = []
    lookup = {}

    def visit(left, right):
        # Only the four admissible row/column masks are part of the logical state.
        state = left[2:] + right[2:]
        if state in lookup:
            return lookup[state]
        uncovered = [index for index, orbit in enumerate(PHASES)
                     if not witness(left, orbit) and not witness(right, orbit)]
        check(uncovered, 'Found an unexpected complete cover')
        index = min(uncovered, key=lambda k: len(choices(left, PHASES[k])) +
                                              len(choices(right, PHASES[k])))
        cell_orbit = PHASES[index]
        children = 0
        for side, box in enumerate((left,right)):
            for phase in choices(box, cell_orbit):
                if box[2:] == (ALL,ALL) and phase != 0:
                    continue
                child = extend(box, *cell_orbit[phase])
                number = visit(left,child) if side else visit(child,right)
                # The formal checker reads one 13-bit index per side and phase.
                children |= number << (13 * (7*side + phase))
        if state in lookup:
            return lookup[state]
        number = len(entries)
        check(number < 8192, 'Increase the index width')
        entries.append([*state, *CELLS[index], children])
        lookup[state] = number
        return number

    root = visit(FREE,FREE)
    check(root == len(entries)-1, 'Root order')
    return entries


def counts():
    intersections = {ALL}
    for row in ROWS:
        intersections |= {columns & row for columns in intersections}
    maximal = set()
    for columns in intersections - {0}:
        rows = sum(1 << i for i,row in enumerate(ROWS) if row & columns == columns)
        if rows:
            maximal.add((rows,columns))

    representatives = {min((rotates(a,q),rotates(b,q)) for q in range(7)) for a,b in maximal}
    signatures = {}
    for a,b in sorted(representatives):
        signature = sum(int(witness((a,b),orbit)) << i for i,orbit in enumerate(PHASES))
        signatures.setdefault(signature, [a,b])

    ordered = sorted(signatures)
    histogram = Counter()
    best = 0
    pair = None
    for i, first in enumerate(ordered):
        for second in ordered[i:]:
            covered = (first | second).bit_count()
            histogram[covered] += 1
            if covered > best:
                best = covered
                pair = [signatures[first], signatures[second]]
    return dict(maximal_rectangles=len(maximal), rectangle_orbits=len(representatives),
                distinct_signatures=len(ordered), pairs=sum(histogram.values()),
                best_orbit_cells=best, best_board_cells=7*best, example=pair,
                pair_histogram={str(k):v for k,v in sorted(histogram.items())})


def lean_sources(data):
    group=64
    blocks=[data[i:i+group] for i in range(0,len(data),group)]
    modules={}
    chunkfiles=[]
    for start in range(0,len(blocks),12):
        name=f'PlaneData{start//12}'
        chunkfiles.append(name)
        text='import PlaneCertificate\n\nnamespace Checkpoint133.Plane.Data\n\n'
        for b,records in enumerate(blocks[start:start+12],start):
            text+=f'def block{b} : Array Entry := #[\n'
            text+=',\n'.join('  ⟨⟨%d,%d⟩,⟨%d,%d⟩,%d,%d,%d⟩'%tuple(r) for r in records)+'\n]\n\n'
        modules[name]=text+'end Checkpoint133.Plane.Data\n'
    text=''.join(f'import {f}\n' for f in chunkfiles)+'\nnamespace Checkpoint133.Plane.Data\n\n'
    text+='def chunks : Array (Array Entry) := #['+','.join(f'block{i}' for i in range(len(blocks)))+']\n'
    text+=f'def lookup (i : ℕ) : Entry := (chunks.getD (i/{group}) #[]).getD (i%{group}) default\n\n'
    modules['PlaneLookup']=text+'end Checkpoint133.Plane.Data\n'
    checkfiles=[]
    for start in range(0,len(blocks),6):
        name=f'PlaneChecks{start//6}';checkfiles.append(name)
        text='import PlaneLookup\n\nnamespace Checkpoint133.Plane.Data\n\n'
        for b,records in enumerate(blocks[start:start+6],start):
            text+=f'set_option maxRecDepth 16000 in\nset_option maxHeartbeats 0 in\ntheorem check{b} : checkBlock lookup {b*group} {len(records)}=true := by decide +kernel\n\n'
        modules[name]=text+'end Checkpoint133.Plane.Data\n'
    text=''.join(f'import {f}\n' for f in checkfiles)+'\nnamespace Checkpoint133.Plane\nopen Data\n\n'
    text+=f'theorem allChecked (i : ℕ) (hi : i<{len(data)}) : Verified lookup i := by\n'
    for b,records in enumerate(blocks):
        if b+1<len(blocks):text+=f'  by_cases h{b} : i<{b*group+len(records)}\n  · exact inBlock check{b} (by omega) h{b}\n'
        else:text+=f'  exact inBlock check{b} (by omega) hi\n\n'
    text+=f'theorem twoOrbits (b d : Box) (hb : Good b) (hd : Good d) : ¬ PairCovers b d := by\n  have no := fromTable lookup {len(data)-1} (fun j h => allChecked j (by omega))\n  have left : (lookup {len(data)-1}).l=free := by decide +kernel\n  have right : (lookup {len(data)-1}).r=free := by decide +kernel\n  rw [left,right] at no\n  exact no b d hb hd (freeFits b) (freeFits d)\n\n#print axioms twoOrbits\nend Checkpoint133.Plane\n'
    modules['PlaneTwo']=text
    return modules

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true');args=ap.parse_args()
    records=certificate();sources=lean_sources(records)
    stats=counts();stats['certificate_states']=len(records)
    for filename,content in [(HERE/'plane-results.json',json.dumps(stats,indent=2)+'\n')]+[(HERE/'src'/(name+'.lean'),s) for name,s in sources.items()]:
        if args.write:filename.write_text(content)
        else:check(filename.read_text()==content,'Certificate differs at '+filename.name)
    print(len(records),'certificate states,',stats['pairs'],'orbit pairs,',stats['best_board_cells'],'of 336 cells covered at best.')
if __name__=='__main__':main()
