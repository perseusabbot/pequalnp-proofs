"""Check or regenerate the row signatures, root supports and 84 embeddings."""
import argparse
from itertools import combinations, product
import json
from pathlib import Path
import sys

from theta_check import PRIOR, instance
sys.path.insert(0,str(PRIOR))
from census import graph
from ten_census import orbit

HERE=Path(__file__).resolve().parent


def lean_list(values):
    return '['+','.join(map(str,values))+']'


def tables():
    model,masks,positive,negative=instance()
    width=len(positive)*len(negative)
    def pack(signal):
        return sum((int(bool(p&signal))<<i)+(int(bool(n&signal))<<(width+i))
                   for i,(p,n) in enumerate(product(positive,negative)))
    words=list(map(pack,masks))
    roots=[words[:9]+[words[9+j] for j in range(3) if extra>>j&1] for extra in range(8)]
    data=('import ThetaSearch\n\nnamespace Checkpoint128.Theta\n\n'
          +'def pos : List ℕ := '+lean_list(positive)+'\ndef neg : List ℕ := '+lean_list(negative)
          +'\ndef masks : List ℕ := '+lean_list(masks)+'\ndef palette : List ℕ := '+lean_list(words)
          +'\n\ndef roots : List (List ℕ) := [\n  '+',\n  '.join(map(lean_list,roots))
          +']\n\nend Checkpoint128.Theta\n')
    edges=graph(PRIOR/'src/HeawoodStages.lean')
    ten=json.loads((PRIOR/'ten_census.json').read_text())['ten_edge_masks']
    _,maps=orbit(edges,ten)
    cases=[]
    for mask,perm in maps:
        codes=[0]*14
        for i,v in enumerate(model['vertex_order']):
            codes[perm[v]]=1<<i
        domain=sum(1<<i for i,x in enumerate(codes) if x)
        cases.append(f'  ⟨{mask},{domain},'+lean_list(codes)+'⟩')
    shapes=('import ThetaData\nimport TenLossFloor\n\nnamespace Checkpoint128.Heawood\n\n'
            'structure Shape where\n  mask : ℕ\n  domain : ℕ\n  codes : List ℕ\n\n'
            'def shapes : List Shape := [\n'+',\n'.join(cases)+']\n\nend Checkpoint128.Heawood\n')
    screens=[]
    for case in json.loads((HERE/'boundary.json').read_text())['orbits']:
        mask=case['representative']
        vertices=case['vertex_order']
        codes=[1<<vertices.index(v) if v in vertices else 0 for v in range(14)]
        retained=[i for i in range(21) if not mask>>i&1]
        matching=next(xs for xs in combinations(retained,case['retained_product_lower_bound'])
                      if len({v for i in xs for v in edges[i]})==2*len(xs))
        shape=f'⟨{mask},{sum(1<<v for v in vertices)},'+lean_list(codes)+'⟩'
        fields=[shape,str(case['gate_cap']),lean_list(matching),lean_list(case['regular_signals']),
                lean_list(case['positive_rows']),lean_list(case['maximal_negative_rows'])]
        screens.append('  ⟨'+','.join(fields)+'⟩')
    sample_data=('import ThetaGeometry\nimport BoundaryRows\n\nnamespace Checkpoint128.Heawood\n\n'
                 'structure Screen where\n  shape : Shape\n  cap : ℕ\n  matching : List (Fin 21)\n'
                 '  signals : List ℕ\n  positives : List ℕ\n  negatives : List ℕ\n\n'
                 'def screens : List Screen := [\n'+',\n'.join(screens)+']\n\nend Checkpoint128.Heawood\n')
    return {'ThetaData.lean':data,'ThetaShapes.lean':shapes,'ElevenSamples.lean':sample_data}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,help='write regenerated Lean files into this directory')
    args=ap.parse_args()
    for name,content in tables().items():
        if args.output:
            args.output.mkdir(parents=True,exist_ok=True)
            (args.output/name).write_text(content)
        elif (HERE/'src'/name).read_text()!=content:
            raise ValueError('Regeneration differs for '+name)
    print('Regenerated all three Lean data tables.')


if __name__=='__main__':
    main()
