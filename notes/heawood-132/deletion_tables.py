"""Reconstruct the finite deletion placements and check every choice of a bottom gate."""
import argparse
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'heawood-131'))
from geometry131 import GROUP, moved, require
from transport import EDGES


def bit(t,v):
    return bool(t & (1 << v))


def vertices(t):
    return [v for v in range(14) if bit(t,v)]


def neighbors(t,v):
    return sum(1 << (b if a==v else a) for a,b in EDGES if v in (a,b)
               and bit(t,b if a==v else a))


def charge(t,u,hot,op,x,y):
    """Count the original constant labels with private rows, then the fresh label."""
    if bit(u,x) and bit(u,y):
        return None
    visible=0
    for v in vertices(t & ~u):
        allowed=neighbors(t,v)
        if v in (x,y):
            other=y if v==x else x
            allowed &= ~(neighbors(t,other) if op else (1<<other))
        visible+=bool(allowed)
    def fixed(v):
        return None if bit(u,v) else v==hot
    a,b=fixed(x),fixed(y)
    fresh_constant=(a is not None and b is not None) or a==bool(op) or b==bool(op)
    return 1+visible+int(fresh_constant)


def numbers(entries):
    return '['+','.join(map(str,entries))+']'


def generate(data, prefix='rank', module='DeletionRanks', initial='InducedCertificate', seeded=None):
    seeded=seeded or {}
    sources={}
    previous=initial
    items=data['nodes']
    for block in range((len(items)+3)//4):
        text='import '+previous+'\n\nnamespace Checkpoint132.Induced\n\n'
        for t,k in items[4*block:4*block+4]:
            branches=data['steps'].get(str(t),[])
            name=prefix+str(t)
            if not branches:
                if t in seeded:
                    text+=f'theorem {name} : Floor {t} {k} := {seeded[t]}\n\n'
                else:
                    require(k<=t.bit_count()-1,'Missing seed')
                    text+=f'theorem {name} : Floor {t} {k} := inputFloor (by decide +kernel) (by decide +kernel)\n\n'
                continue
            choices=[]
            for u,c,level,hot in branches:
                require(u!=t and not(u&~t),'Invalid restriction')
                require(hot==14 or (bit(t&~u,hot) and not neighbors(u,hot)),'Invalid true vertex')
                perm=next(p for _,p in GROUP if moved(u,p)==c)
                choices.append(f'⟨{u},{c},{level},{hot},{numbers(perm)}⟩')
            lookup=[]
            for op in (0,1):
                for x in range(14):
                    for y in range(14):
                        if x==y or not(bit(t,x) and bit(t,y)):
                            lookup.append(0)
                            continue
                        valid=[j for j,(u,c,level,hot) in enumerate(branches)
                               if (cost:=charge(t,u,hot,op,x,y)) is not None and level+cost>=k]
                        require(valid,'Incomplete first-gate cover')
                        lookup.append(valid[0])
            choices_name='choices'+name
            lookup_name='lookup'+name
            text+=f'private def {choices_name} : List Choice := [\n  '+',\n  '.join(choices)+']\n'
            text+=f'private def {lookup_name} : List ℕ := '+numbers(lookup)+'\n\n'
            text+=f'''set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem {name} : Floor {t} {k} := by
  apply certified {choices_name} {lookup_name}
  · intro r hr
    simp only [{choices_name},List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with '''+'|'.join('rfl' for _ in branches)+'\n'
            for u,c,level,hot in branches:
                text+=f'    · exact floorMono {prefix}{c} (by decide +kernel)\n'
            text+=f'''  · have good : {choices_name}.all (fun r => decide (Verified {t} r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

'''
        for t,_ in items[4*block:4*block+4]:
            text+='#print axioms '+prefix+str(t)+'\n'
        previous=module+str(block)
        sources[previous]=text+'end Checkpoint132.Induced\n'
    return sources


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true')
    write=ap.parse_args().write
    sources=generate(json.loads((HERE/'deletions.json').read_text()))
    for name,content in sources.items():
        path=HERE/'src'/(name+'.lean')
        if write:
            path.write_text(content)
        else:
            require(path.read_text()==content,'Lean table differs in '+name)
    print('Verified every ordered bottom gate in the deletion tables.')


if __name__=='__main__':
    main()
