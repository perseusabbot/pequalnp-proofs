"""Count the moving rectangle pairs required by involutions that exchange the two axes."""
from collections import Counter
import json
import os
from pathlib import Path
import subprocess
import tempfile

from geometry import ACTIONS, HERE, IDENTITY, ROWS, bits, group, maximal_rectangles, permute, require, union
from search import encode, fewer_movers, four, perm_table


def inventory(elements):
    absolute=Counter()
    for g in elements:
        if g[0]>=21 and g.translate(perm_table(g))==IDENTITY:
            absolute[sum(not (ROWS[i] >> (g[i]-21) & 1) for i in range(21))]+=1
    return absolute


def first_two(words, real_words, central, lookup, required):
    # A maximum-area first member hits a sixth of the boundary. Of the other
    # five, at least one hits a fifth of the residual left by the first.
    todo={i for i,w in enumerate(words) if 6*w.bit_count()>=required.bit_count()}
    first=[]
    while todo:
        i=min(todo)
        images={lookup[permute(real_words[i],u)] for u in central}
        require(images<=todo,'Overlapping first pairs')
        todo-=images
        first.append(i)
    unions=set()
    for i in first:
        a=words[i]
        left=required & ~a
        subgroup=[u for u in central if lookup[permute(real_words[i],u)]==i]
        seconds={j for j,b in enumerate(words) if j!=i and b.bit_count()<=a.bit_count()
                 and 5*(b&left).bit_count()>=left.bit_count()}
        while seconds:
            j=min(seconds)
            images={lookup[permute(real_words[j],u)] for u in subgroup}
            require(images<=seconds,'Overlapping second pairs')
            seconds-=images
            unions.add(a|words[j])
    return len(first),sorted(unions)


def analyze(d, elements, maximal, total, binary):
    a=d['columns_for_rows']
    require(sorted(a)==list(range(21)),'Invalid column partner')
    b=[a.index(i) for i in range(21)]
    g=bytes([21+j for j in a]+b)
    require(g in elements and g.translate(perm_table(g))==IDENTITY,'Duality is outside the group')
    central=[u for u in elements if u.translate(perm_table(g))==g.translate(perm_table(u))]
    board=[permute(w,b) for w in ROWS]
    require(all(board[x]>>y&1==board[y]>>x&1 for x in range(21) for y in range(21)),'Asymmetric board')
    absolute={x for x in range(21) if not (board[x]>>x & 1)}
    count=len(absolute)
    require(len(central)*total[count]==len(elements),'Conjugates do not exhaust this type')
    # A fixed rectangle has equal shores in these coordinates. Every allowed
    # edge with two looped ends is in the legal square on its two ends.
    cells=[(x,y) for x in range(21) for y in range(x,21)
           if board[x]>>y&1 and (x in absolute or y in absolute)]
    index={p:i for i,p in enumerate(cells)}
    required=(1<<len(cells))-1
    def footprint(box):
        x,y=box
        return union(1<<index[p] for i in bits(x) for j in bits(y)
                     if (p:=tuple(sorted((i,j)))) in index)
    boxes=sorted({tuple(sorted((u,permute(v,b)))) for u,v in maximal if u!=permute(v,b)})
    words=[footprint(box) for box in boxes]
    witness=[tuple(t) for t in d['boundary_witness']]
    for u,v in witness:
        require(u and v and u!=v and all(v & ~board[i]==0 for i in bits(u)),'Illegal moving rectangle')
    require(union(footprint(z) for z in witness)==required,'Incomplete moving-pair witness')
    result=dict(absolute_vertices=count,conjugate_polarities=total[count],centralizer=len(central),
                boundary_cells=len(cells),moving_maximal_pairs=len(boxes),upper_moving_pairs=len(witness))
    if count==5:
        fewer_movers(required,words)
        result['lower_moving_pairs']=4
    else:
        require(count==9,'Unexpected polarity type')
        # Each normalized first pair has at least one fifth of the boundary.
        def real(box):
            return encode((box[0],permute(box[1],a)))
        lookup={w:i for i,box in enumerate(boxes) for w in (real(box),real(box[::-1]))}
        require(len(lookup)==2*len(boxes),'Moving-pair inventory incomplete')
        todo={i for i,w in enumerate(words) if 5*w.bit_count()>=len(cells)}
        reps=[]
        while todo:
            i=min(todo)
            images={lookup[permute(real(boxes[i]),u)] for u in central}
            require(images<=todo,'Polarity leader classes overlap')
            todo-=images
            reps.append((words[i],len(images)))
        result['five_pair_test']=four(binary,len(cells),words,reps)
        first,unions=first_two(words,[real(box) for box in boxes],central,lookup,required)
        test=four(binary,len(cells),words,[(w,1) for w in unions])
        result['six_pair_test']=dict(first_classes=first,distinct_unions=len(unions),final_queries=test['final_queries'])
        result['lower_moving_pairs']=7
    return result


def main():
    elements=group()
    counts=inventory(elements)
    require(set(counts)=={5,9},'Unexpected side-swapping involution')
    maximal=maximal_rectangles()
    with tempfile.TemporaryDirectory() as tmp:
        binary=Path(tmp)/'four'
        subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++20',str(HERE/'four.cpp'),'-o',str(binary)],check=True)
        out={name:analyze(d,elements,maximal,counts,binary) for name,d in ACTIONS['dualities'].items()}
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
