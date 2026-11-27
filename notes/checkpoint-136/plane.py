"""Projective frames and reconstruction on the 21-point incidence board."""
from itertools import combinations
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'checkpoint-135'))
from geometry import IDENTITY, ROWS, bits, group, require

BOARD = (1<<21)-1
LINES_AT = [BOARD ^ r for r in ROWS]
POINTS_ON = [sum(1<<p for p in range(21) if LINES_AT[p]>>l&1) for l in range(21)]


def inverse(p):
    inv=bytearray(len(p))
    for i,j in enumerate(p):
        inv[j]=i
    return bytes(inv)


def table(p):
    return bytes.maketrans(IDENTITY,p)


def common(a,b,masks):
    intersection=masks[a]&masks[b]
    require(a!=b and intersection.bit_count()==1,'Join or meet is not unique')
    return intersection.bit_length()-1


def frame_data():
    points=range(21)
    a,b=0,1
    ab=common(a,b,LINES_AT)
    c=next(iter(bits(BOARD^POINTS_ON[ab])))
    ac,bc=(common(x,c,LINES_AT) for x in (a,b))
    d=next(iter(bits(BOARD^(POINTS_ON[ab]|POINTS_ON[ac]|POINTS_ON[bc]))))
    cd=common(c,d,LINES_AT)
    x=common(ab,cd,POINTS_ON)
    e=next(iter(bits(POINTS_ON[ab] & ~((1<<a)|(1<<b)|(1<<x)))))
    allowed=[list(points),[i for i in points if i!=a],list(bits(BOARD^POINTS_ON[ab])),
             list(bits(BOARD^(POINTS_ON[ab]|POINTS_ON[ac]|POINTS_ON[bc]))),
             list(bits(POINTS_ON[ab] & ~((1<<a)|(1<<b)|(1<<x))))]
    seed=[a,b,c,d,e]
    require(list(map(len,allowed))==[21,20,16,9,2],'Frame sizes differ')
    known=set(seed); trace=[]
    while len(known)<42:
        count=len(known)
        for side, masks in [(0,LINES_AT),(1,POINTS_ON)]:
            labels=sorted(z-side*21 for z in known if z//21==side)
            for i,j in combinations(labels,2):
                destination=common(i,j,masks)+(1-side)*21
                if destination not in known:
                    known.add(destination)
                    trace.append([destination,side*21+i,side*21+j])
        require(len(known)>count,'Frame does not determine the board')
    return seed,allowed,trace


def frame_receipt(elements):
    seed,allowed,trace=frame_data()
    axis=[g for g in elements if g[0]<21]
    levels=[]
    for p,out in zip(seed,allowed):
        images={}
        for g in axis:
            images.setdefault(g[p],g)
        require(set(images)==set(out),'Frame stabilizer has an unexpected orbit')
        axis=[g for g in axis if g[p]==p]
        levels.append(dict(point=p,choices=out,remaining=len(axis)))
    require(axis==[IDENTITY] and len(elements)==2*21*20*16*9*2,'Wrong final stabilizer')
    return dict(seed=seed,trace=trace,levels=levels,side_preserving=120960,including_dualities=241920)
