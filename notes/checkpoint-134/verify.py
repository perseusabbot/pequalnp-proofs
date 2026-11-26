"""Check the rotation minima directly and replay the integer weight certificates."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import partial, reduce
from itertools import combinations
import json
from math import gcd
from operator import or_
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SIZE = 21
ALL = (1 << SIZE) - 1
DATA = json.loads((HERE / 'board.json').read_text())
ROWS = [ALL ^ w for w in DATA['forbidden_row_masks']]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask -= low


def union(masks):
    return reduce(or_, masks, 0)


def permute(mask, permutation):
    return sum(1 << permutation[i] for i in bits(mask))


def rotate_rectangle(box, p, q):
    return permute(box[0], p), permute(box[1], q)


def cycle(start, successor):
    out = []
    item = start
    while item not in out:
        out.append(item)
        item = successor(item)
    require(item == start, 'Expected a permutation cycle')
    return out


def validate_action(p, q, order):
    for permutation in (p, q):
        require(sorted(permutation) == list(range(SIZE)), 'Non-bijective axis')
        require(max(len(cycle(i, lambda x: permutation[x])) for i in range(SIZE)) == order,
                'Unexpected order')
    require(all(permute(ROWS[i], q) == ROWS[p[i]] for i in range(SIZE)), 'Action changes board')


def maximal_rectangles():
    # Every nonempty rectangle can first be extended to the common columns of
    # its rows, then to all rows containing those columns. This construction
    # commutes with each pair of row and column permutations in this checker.
    columns = {ALL}
    for row in ROWS:
        columns |= {word & row for word in columns}
    result = set()
    for word in columns - {0}:
        rows = sum(1 << i for i, row in enumerate(ROWS) if row & word == word)
        if rows:
            result.add((rows, word))
    return result


def quotient(rectangles, p, q, order):
    validate_action(p, q, order)
    cell_index = {}
    cells = []
    for i, word in enumerate(ROWS):
        for j in bits(word):
            if (i, j) in cell_index:
                continue
            index = len(cells)
            cells.append((i, j))
            for point in cycle((i, j), lambda xy: (p[xy[0]], q[xy[1]])):
                cell_index[point] = index
    fixed, moving, seen = [], [], set()
    for box in sorted(rectangles):
        if box in seen:
            continue
        group = cycle(box, lambda r: rotate_rectangle(r, p, q))
        require(all(r in rectangles for r in group) and len(group) in (1, order), 'Bad rectangle orbit')
        seen.update(group)
        a, b = box
        mask = union(1 << cell_index[i, j] for i in bits(a) for j in bits(b))
        (fixed if len(group) == 1 else moving).append((box, mask))
    require(seen == rectangles, 'Orbit inventory incomplete')
    return cells, fixed, moving


def check_cover(cover, p, q, size):
    family = set(tuple(z) for z in cover)
    require(len(family) == size, 'Wrong witness size')
    require({rotate_rectangle(r, p, q) for r in family} == family, 'Witness is not invariant')
    for i, need in enumerate(ROWS):
        got = union(b for a, b in family if a >> i & 1)
        require(got == need, f'Witness row {i} differs')


def pair_classes(fixed):
    boxes = [box for box, _ in fixed]
    forbidden = set(bits(ALL ^ ROWS[0]))
    permutations = []
    for a in range(1, SIZE):
        if gcd(a, SIZE) != 1:
            continue
        for b in range(SIZE):
            if {(a * j + b) % SIZE for j in forbidden} != forbidden:
                continue
            for h in range(7):
                for dual in (False, True):
                    scale = -a if dual else a
                    p = [(scale*x + h) % SIZE for x in range(SIZE)]
                    q = [(scale*x + h + b) % SIZE for x in range(SIZE)]
                    images = []
                    for rows, columns in boxes:
                        x, y = (columns, rows) if dual else (rows, columns)
                        images.append(boxes.index((permute(x, p), permute(y, q))))
                    for x in range(SIZE):
                        for y in range(SIZE):
                            r, c = (p[y], q[x]) if dual else (p[x], q[y])
                            require(ROWS[r] >> c & 1 == ROWS[x] >> y & 1, 'Pair map changes board')
                    require(scale % 3 != 0, 'Pair map does not conjugate the rotation')
                    permutations.append(images)
    counts = Counter(min(tuple(sorted((p[i], p[j]))) for p in permutations)
                     for i, j in combinations(range(len(fixed)), 2))
    require(counts == {(0,1):42, (0,4):21, (0,6):21, (0,13):7}, 'Fixed pair classes differ')
    return {str(k[1]): v for k, v in sorted(counts.items())}


def replay_weights(cuts, pools, slots, cell_count, forbidden):
    # Pack only nonnegative integers. The sum of all cell weights is below one
    # lane, so summing the weights of any subset cannot carry between lanes.
    width = 24
    lane = (1 << width) - 1
    for c in cuts:
        w = c['weights']
        require(len(w) == cell_count and all(type(x) is int and x >= 0 for x in w), 'Invalid cell weight')
        require(0 < sum(w) == c['total'] <= lane, 'Invalid total')
        require(all(w[i] == 0 for i in bits(forbidden)), 'Fixed pair touches a positive weight')
    coins = [sum(c['weights'][j] << (width*k) for k,c in enumerate(cuts)) for j in range(cell_count)]
    live = [[sum(coins[i] for i in bits(mask)) for mask in set(pool)] for pool in pools]
    for k, c in enumerate(cuts):
        caps = c.get('caps', [c.get('cap')])
        require(len(caps) == len(slots) and all(type(x) is int and x >= 0 for x in caps), 'Bad cap')
        ceiling = sum(n * cap for n,cap in zip(slots,caps))
        for family, cap in enumerate(caps):
            remaining = []
            for word in live[family]:
                score = word >> (width*k) & lane
                require(score <= cap, 'Surviving candidate exceeds the asserted cap')
                if score + ceiling - cap >= c['total']:
                    remaining.append(word)
            live[family] = remaining
    require(all(not family for family in live), 'Integer eliminations left a candidate')
    return len(cuts)


def direct_four(need, movers):
    # Choose the first mask of maximum area, the second of maximum additional
    # area, then the better of the two remaining masks. Cell postings answer
    # the last superset query exactly. Ties follow the order in the lists.
    require(need!=0, 'The fixed pair already covers the board')
    words = sorted({m & need for m in movers}, key=lambda w: (-w.bit_count(), w))
    postings = {j: sum(1 << i for i,w in enumerate(words) if w >> j & 1) for j in bits(need)}
    sizes = {j: p.bit_count() for j,p in postings.items()}
    examined = 0
    for i, a in enumerate(words):
        if 4 * a.bit_count() < need.bit_count():
            break
        left = need & ~a
        require(left!=0, 'A single moving group covers the residual')
        n = left.bit_count()
        others = sorted(((gain, w) for w in words[i+1:]
                         if (gain := (w & left).bit_count()) >= n - 2*a.bit_count()), reverse=True)
        for j, (gain, b) in enumerate(others):
            if 3*gain < n:
                break
            rest = left & ~b
            require(rest!=0, 'Two moving groups cover the residual')
            half = (rest.bit_count()+1)//2
            for bound, c in others[j+1:]:
                if bound < half:
                    break
                if (c & rest).bit_count() < half:
                    continue
                examined += 1
                missing = rest & ~c
                possible = (1 << len(words))-1
                for x in sorted(bits(missing), key=sizes.get):
                    possible &= postings[x]
                    if not possible:
                        break
                require(not possible, 'Four moving orbits cover the residual')
    return examined


def all_pair_queries(full, fixes, movers, jobs):
    needs=[full & ~(a | b) for a,b in combinations(fixes,2)]
    search=partial(direct_four,movers=movers)
    if jobs==1:
        yield from map(search,needs)
    else:
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            yield from pool.map(search,needs,chunksize=2)


def native_pairs(fixes, movers):
    payload=''.join(f'{m & ((1<<64)-1)} {m >> 64}\n' for m in [*fixes,*movers])
    with tempfile.TemporaryDirectory() as temp:
        binary=Path(temp)/'reference'
        subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(HERE/'reference.cpp'),'-o',str(binary)],check=True)
        output=subprocess.check_output([str(binary)],input=payload,text=True).split()
    excluded,queries=map(int,output)
    require(excluded==91,'Incomplete native fixed-pair search')
    return dict(excluded=excluded,total_last_queries=queries)


def boundary_triples(full, fixes, movers):
    boundary = full & ~union(fixes)
    require(boundary.bit_count()==49, 'Order-three boundary')
    sizes = [(w & boundary).bit_count() for w in movers]
    require(max(sizes)==17 and 16 not in sizes, 'Three-orbit area bound')
    leaders = [i for i,n in enumerate(sizes) if n==17]
    triples = set()
    for i,j in combinations(leaders,2):
        missing = boundary & ~(movers[i] | movers[j])
        if missing.bit_count() <= 17:
            for k,w in enumerate(movers):
                if w & missing == missing:
                    triples.add(tuple(sorted((i,j,k))))
    counts = Counter()
    for seq in triples:
        need = full & ~union(movers[i] for i in seq)
        best = next(n for n in range(len(fixes)+1) if any(
            not need & ~union(fixes[i] for i in pick) for pick in combinations(range(len(fixes)),n)))
        counts[best] += 1
    require(counts == {7:14}, 'Three-orbit completions differ')
    return len(triples)


def order_five(rectangles):
    info = DATA['order_five']
    p,q = info['row_permutation'],info['column_permutation']
    cells, fixed, moving = quotient(rectangles,p,q,5)
    full = (1 << len(cells))-1
    boundary = full & ~union(m for _,m in fixed)
    masks = {m for _,m in moving}
    signatures = {w & boundary for w in masks}
    best = max((u | v).bit_count() for u,v in combinations(signatures,2))
    require(best == 41 < boundary.bit_count() == 46, 'Two order-five orbits reach the boundary')
    words = sorted(masks, key=lambda w: (-w.bit_count(),w))
    postings = [sum(1 << i for i,w in enumerate(words) if w >> j & 1) for j in range(len(cells))]
    for i, a in enumerate(words):
        if 3*a.bit_count() < len(cells):
            break
        left = full & ~a
        for b in words[i+1:]:
            if 2*(b & left).bit_count() < left.bit_count():
                continue
            possible = (1 << len(words))-1
            for j in bits(left & ~b):
                possible &= postings[j]
                if not possible:
                    break
            require(not possible, 'Three order-five orbits suffice')
    fixed_box, *generators = map(tuple,info['fixed_then_generators'])
    require(rotate_rectangle(fixed_box,p,q)==fixed_box, 'First witness rectangle is not fixed')
    cover = [fixed_box]
    for generator in generators:
        cover += cycle(generator,lambda r:rotate_rectangle(r,p,q))
    check_cover(cover,p,q,16)
    return dict(cells=len(cells), fixed=len(fixed), moving=len(moving), boundary=46,
                best_two_on_boundary=best, minimum=16)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--direct',action='store_true',help='Also run the independent four-orbit search')
    parser.add_argument('--all-pairs',action='store_true',help='Run the direct search on all 91 fixed pairs')
    parser.add_argument('--jobs',type=int,default=1,help='Python workers for the full 91-pair search')
    args=parser.parse_args()
    if args.jobs<1:
        parser.error('--jobs must be positive')
    rectangles=maximal_rectangles()
    require(len(rectangles)==25235 and sum(row.bit_count() for row in ROWS)==336, 'Board inventory')
    p=[(i+7)%SIZE for i in range(SIZE)]
    cells,fixed,moving=quotient(rectangles,p,p,3)
    require(len(cells)==112 and len(fixed)==14 and len(moving)==8407, 'Order-three inventory')
    require(cells==[(i,j) for i in range(7) for j in bits(ROWS[i])], 'Weight indexing differs')
    fixes=[m for _,m in fixed]
    movers=[m for _,m in moving]
    full=(1<<len(cells))-1
    classes=pair_classes(fixed)
    result=dict(maximal_rectangles=len(rectangles),fixed=len(fixed),moving=len(moving),
                pair_class_sizes=classes,order_three_minimum=15,weight_tests={})
    check_cover(DATA['published_fifteen'],p,p,15)
    result['boundary_triples']=boundary_triples(full,fixes,movers)
    for k,f in ((2,14),(3,5)):
        cuts=json.loads((HERE/'weights'/f'mixedcert-{k}.json').read_text())
        result['weight_tests'][f'{k} moving, {f} fixed']=replay_weights(cuts,[fixes,movers],[f,k],len(cells),0)
    for j in map(int,classes):
        forbidden=fixes[0] | fixes[j]
        cuts=json.loads((HERE/'weights'/f'target-{j}.json').read_text())
        result['weight_tests'][f'4 moving, fixed pair 0/{j}']=replay_weights(cuts,[movers],[4],len(cells),forbidden)
        if args.direct or args.all_pairs:
            result.setdefault('direct_four_last_queries',{})[str(j)]=direct_four(full & ~forbidden,movers)
    if args.all_pairs:
        tested=Counter()
        for done,queried in enumerate(all_pair_queries(full,fixes,movers,args.jobs),start=1):
            tested[queried]+=1
            if done in (21,45,66,91):
                print(f'{done} of 91 fixed pairs excluded',file=sys.stderr,flush=True)
        require(sum(tested.values())==91,'Fixed pair inventory incomplete')
        result['all_fixed_pairs']=dict(excluded=sum(tested.values()),
            total_last_queries=sum(n*count for n,count in tested.items()),
            last_query_histogram=dict(sorted(tested.items())))
        result['native_fixed_pairs']=native_pairs(fixes,movers)
    result['order_five']=order_five(rectangles)
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
