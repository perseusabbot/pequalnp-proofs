"""Enumerate the minimal obstructions to extension to a legal 6-by-6 rectangle."""
import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'checkpoint-137'))
from rectangles import BOARD, ROWS, bits, group, label_patterns, maximal_rectangles, perm_mask, require, six_rectangles


def subsets(mask):
    sub = mask
    while sub:
        yield sub
        sub = (sub-1) & mask
    yield 0


def support_orbits(boxes, moves):
    supported = {u for a,b in boxes for u in subsets(a | b << 21)}
    minimal = set()
    for w in supported:
        for v in range(w.bit_length(),42):
            u = w | 1 << v
            if u in supported or any(u ^ (1 << i) not in supported for i in bits(w)):
                continue
            a,b = u & BOARD,u >> 21
            if all(not(b & ~ROWS[i]) for i in bits(a)):
                minimal.add(u)
    # Every minimal obstruction is generated from its largest label and the
    # supported set obtained by deleting that label.
    shapes = []
    left = minimal.copy()
    while left:
        root = min(left)
        orbit,queue = {root},[root]
        for w in queue:
            for move in moves:
                image = move(w)
                if image not in orbit:
                    orbit.add(image)
                    queue.append(image)
        require(orbit <= left,'Support orbits overlap')
        left -= orbit
        shapes.append(dict(rows=root & BOARD,cols=root >> 21,count=len(orbit)))
    return len(supported),dict(sorted(Counter(u.bit_count() for u in minimal).items())),shapes


def cell_obstructions(a, b, all_boxes, postings, total):
    """A minimal cell obstruction must supply a cell incident with each marked label."""
    def fits(cells):
        possible = (1 << total)-1
        for cell in cells:
            possible &= postings[cell]
        return bool(possible)
    hosts = [(u,v) for u,v in all_boxes if not(a & ~u or b & ~v)]
    seen,minimal = set(),set()
    for u,v in hosts:
        choices = [[21*r+c for c in bits(v)] for r in bits(a)]
        choices += [[21*r+c for r in bits(u)] for c in bits(b)]
        for selection in product(*choices):
            cells = tuple(sorted(set(selection)))
            if cells in seen:
                continue
            seen.add(cells)
            if all(fits(cells[:i]+cells[i+1:]) for i in range(len(cells))):
                require(not fits(cells),'The marked labels admit an extension')
                minimal.add(cells)
    return minimal


def cell_image(g, cell):
    p,q = g[cell//21],g[21+cell%21]
    if p >= 21:
        p,q = q,p
    return 21*p+q-21


def count_cell_orbits(elements, normalized):
    # A global orbit meets the normalized set whenever an underlying support
    # obstruction is taken to its representative. Different markings can normalize
    # the same cell set. Intersecting entire orbits removes this duplication.
    left,classes = set(normalized),[]
    while left:
        cells = min(left)
        stabilizer = 0
        for g in elements:
            image = tuple(sorted(cell_image(g,v) for v in cells))
            if image == cells:
                stabilizer += 1
            left.discard(image)
        require(stabilizer > 0 and len(elements)%stabilizer == 0,'Wrong cell-set stabilizer')
        classes.append(dict(cells=[[i//21,i%21] for i in cells],stabilizer=stabilizer,
                            count=len(elements)//stabilizer))
    return classes


def report():
    boxes = six_rectangles()
    elements = group()
    grids = maximal_rectangles()
    n,by_size,shapes = support_orbits(boxes,[perm_mask(g) for g in elements[1:5]])
    postings = {21*r+c:sum(1<<i for i,(a,b) in enumerate(boxes) if a>>r & b>>c & 1)
                for r,w in enumerate(ROWS) for c in bits(w)}
    normalized = set()
    for shape in shapes:
        obs = cell_obstructions(shape['rows'],shape['cols'],grids,postings,len(boxes))
        shape['cell_sets_through_marking'] = dict(sorted(Counter(map(len,obs)).items()))
        normalized |= obs
    classes = count_cell_orbits(elements,normalized)
    global_counts = Counter()
    for cls in classes:
        global_counts[len(cls['cells'])] += cls['count']
    even = sorted({tuple(j for j,(c,d) in enumerate(boxes) if (a&c).bit_count()%2==0) for a,b in boxes})
    require([len(x) for x in even] == [56]*3 and len(set().union(*even)) == 168,'Wrong parity partition')
    palette = {j:i for i,cls in enumerate(even) for j in cls}
    pencils,triples = label_patterns(boxes)
    require(all(sorted(palette[i] for i in t)==[0,1,2] for ts in triples for t in ts),'Wrong triple colors')
    # An independent obstruction to a 5-by-5 off-diagonal incidence pattern.
    # Keep one missing cell fixed, enumerate four alternatives through it, then
    # test all remaining maximum rectangles as the fifth one.
    cells = [sum(b << (21*i) for i in bits(a)) for a,b in boxes]
    here = list(bits(postings[1]))
    distinct,possible,extend = 0,0,0
    for choice in combinations(here,4):
        pockets = []
        for skip in choice:
            same = -1
            for j in choice:
                if j != skip:
                    same &= cells[j]
            pockets.append(same & ~cells[skip])
        distinct += 1
        if all(pockets):
            possible += 1
            extend += sum(not(mask&2) and all(mask&w for w in pockets) for mask in cells)
    require((distinct,possible,extend)==(3060,360,0),'Unexpected five-witness pattern')
    return dict(supported_label_sets=n,minimal_supports_by_size=by_size,support_orbits=shapes,
                minimal_cell_orbits=classes,minimal_legal_cell_sets_by_size=dict(sorted(global_counts.items())),
                colors=even,colors_per_complete_triple=[1,1,1],
                anchored_four_subsets=distinct,subsets_with_four_nonempty_pockets=possible,
                five_witness_extensions=extend)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    data = report()
    serialized = json.dumps(data,indent=2)+'\n'
    if args.output:
        args.output.write_text(serialized)
    else:
        require(serialized == (HERE/'geometry.json').read_text(),'Geometry receipt differs')
    print(len(data['support_orbits']),'support orbits,',len(data['minimal_cell_orbits']),
          'cell-set orbits,',data['minimal_legal_cell_sets_by_size'])
