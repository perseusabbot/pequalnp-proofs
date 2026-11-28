"""Build the normalized pair anchors and their action on eligible third rectangles."""
import argparse
from collections import Counter
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'checkpoint-138'))
from replay import bits, group, inventory, prefix, require, six_rectangles
from rectangles import BOARD, maximal_rectangles


def build_input():
    pairs,_ = inventory()
    geo = json.loads((HERE.parent/'checkpoint-137/results.json').read_text())['geometry']
    shapes = [tuple(sorted(r['shape'])) for r in geo['shape_orbits'] if 'roots' in r]
    ordinary = sorted(a | b<<21 for a,b in maximal_rectangles() if a.bit_count()*b.bit_count()!=36)
    index = {w:i for i,w in enumerate(ordinary)}
    ranks = [shapes.index(tuple(sorted(((w&BOARD).bit_count(),(w>>21).bit_count())))) for w in ordinary]
    counts = Counter(ranks)
    elements = group()
    labels = {w:list(bits(w)) for w in {x for p in pairs for x in p[:2]}}
    maps,anchors = {},[]
    from itertools import groupby
    for a,items in groupby(pairs,key=lambda p:p[0]):
        fixed = [g for g in elements if all(a>>g[i]&1 for i in labels[a])]
        r = ranks[index[a]]
        require(counts[r]*len(fixed)==len(elements),'First stabilizer size differs')
        for _,b,n in items:
            stabilizer = [maps.setdefault(g,len(maps)) for g in fixed if all(b>>g[i]&1 for i in labels[b])]
            require(len(stabilizer)*n==len(fixed),'Marked-pair stabilizer size differs')
            anchors.append([index[a],index[b],len(stabilizer),*stabilizer])
    def row(x):
        return ' '.join(map(str,x))+'\n'
    require(len(anchors)==2487 and len(ordinary)==25067,'Board inventory differs')
    return (prefix(six_rectangles())+row([len(ordinary)])+
            ''.join(row([w&BOARD,w>>21,r]) for w,r in zip(ordinary,ranks))+
            row([len(elements),len(maps)])+''.join(row(g) for g in maps)+
            row([len(anchors)])+''.join(row(p) for p in anchors))


if __name__=='__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('output',type=Path)
    dest = ap.parse_args().output
    dest.write_text(build_input())
