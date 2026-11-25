"""Build the four signed-column problems and their induced-graph deletion certificate."""
import argparse
import json
from deletion_tables import HERE, generate, numbers, require, vertices
from geometry131 import ALL, sample

CASES=[(1959,10),(1963,10),(2019,11),(3771,12)]
WIDTH=110


def rows(t):
    graph=sample(ALL,t)
    pairs=[(p,n) for p in graph['positive_rows'] for n in graph['negative_rows']]
    require(0<len(pairs)<=WIDTH,'Unsupported number of distinctions')
    def column(v):
        return sum((((p>>v)&1)<<i) + (((n>>v)&1)<<(WIDTH+i))
                   for i in range(WIDTH) for p,n in [pairs[i%len(pairs)]])
    return [column(v) for v in range(14)]


def seed_data():
    text='import InducedSeeds\n\nnamespace Checkpoint132.Induced\nopen Checkpoint128.Theta\n\n'
    for t,k in CASES:
        packed=rows(t)
        order=vertices(t)
        text+=f'def columns{t} : List ℕ := '+numbers(packed[v] for v in order)+'\n'
        text+=f'private def sig{t} (v : Slot {t}) : ℕ := '+numbers(packed)+'.getD v.val.val 0\n'
        text+=f'private def ports{t} : List (Slot {t}) := ['+','.join(f'⟨{v},by decide⟩' for v in order)+']\n'
        text+=f'''set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem small{t} (closed : search {k} columns{t}=false) : Floor {t} {k+1} := by
  apply seedFloor sig{t} ports{t} (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact (show ports{t}.map sig{t}=columns{t} by decide +kernel) ▸ closed

#print axioms small{t}

'''
    text+='def SeedChecks : Prop :=\n  '+' ∧\n  '.join(f'search {k} columns{t}=false' for t,k in CASES)+'\n\nend Checkpoint132.Induced\n'
    return text


def seed_ranks():
    data=json.loads((HERE/'seed-deletions.json').read_text())
    access=['.1','.2.1','.2.2.1','.2.2.2']
    seeds={t:f'small{t} checks'+path for (t,_),path in zip(CASES,access)}
    files=generate(data,'seed','SeedRanks','SeedData',seeds)
    for name,txt in files.items():
        for t,_ in data['nodes']:
            txt=txt.replace(f'theorem seed{t} :',f'theorem seed{t} (checks : SeedChecks) :')
            txt=txt.replace(f'floorMono seed{t} ',f'floorMono (seed{t} checks) ')
        files[name]=txt
    return files


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true')
    write=ap.parse_args().write
    for name,value in {'SeedData':seed_data(),**seed_ranks()}.items():
        dest=HERE/'src'/(name+'.lean')
        if write:
            dest.write_text(value)
        else:
            require(dest.read_text()==value,'Signed seed table mismatch')
    print('Verified four finite row sets and 34 deletion placements for the 21-gate reduction.')


if __name__=='__main__':
    main()
