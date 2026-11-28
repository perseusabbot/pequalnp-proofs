"""Normalize small dominating sets of row and column labels under the checked board symmetries."""
import argparse
from itertools import combinations
from pathlib import Path
from inventory import group, require
from rectangles import BOARD, COLS, ROWS, bits, perm_mask


def masks(values, count):
    for take in combinations(values,count):
        yield sum(1<<i for i in take)


def image(g, indices, offset):
    return sum(1<<(g[offset+i]-offset) for i in indices)


def low_sets(maximum):
    # Duality permits the smaller set on the point side. At equal sizes we retain both orientations.
    elements = [g for g in group() if g[0]<21]
    roots = []
    for k in range(1,maximum//2+1):
        if 4*k+maximum-k<20:
            continue
        remaining = set(masks(range(21),k))
        while remaining:
            p = min(remaining)
            indices = list(bits(p))
            orbit = {image(g,indices,0) for g in elements}
            require(orbit<=remaining,'Row-set orbits intersect')
            remaining -= orbit
            generators = [g for g in elements if all(p>>g[i]&1 for i in indices)]
            require(len(orbit)*len(generators)==len(elements),'Wrong row-set stabilizer')
            cols = [lambda w,act=perm_mask(g):act(w<<21)>>21 for g in generators]
            need = sum(1<<j for j in range(21) if not (p & (BOARD^COLS[j])))
            for n in range(k,maximum-k+1):
                if n<need.bit_count() or k+4*n<20:
                    continue
                left = set()
                for rest in masks(bits(BOARD^need),n-need.bit_count()):
                    q = need|rest
                    if all(q & (BOARD^ROWS[i]) for i in bits(BOARD^p)):
                        left.add(q)
                while left:
                    q = min(left);orbit_q = {act(q) for act in cols}
                    require(q in orbit_q and orbit_q<=left,'Column-set orbits intersect')
                    left -= orbit_q
                    roots.append((p,q,len(orbit)*len(orbit_q)*(1 if n==k else 2)))
    return sorted(roots,key=lambda x:(x[0].bit_count()+x[1].bit_count(),x[0],x[1]))


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('maximum',type=int)
    ap.add_argument('output',type=Path)
    args=ap.parse_args()
    rows=low_sets(args.maximum)
    args.output.write_text(''.join(' '.join(map(str,r))+'\n' for r in rows))
    print(len(rows),'dominating-set representatives')
