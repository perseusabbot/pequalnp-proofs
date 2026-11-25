"""Lift a circuit on 13 vertices, one neighbor pair, and the triple into posted opening 20."""
import argparse
import json
from pathlib import Path
from itertools import combinations

from deletion_tables import HERE, numbers, vertices
from geometry131 import ALL, GROUP, column, moved, require, sample
from row_tables import star_control

MASK=262143
DOMAIN=16319
CENTER=6
TIPS=(8,9,11)
PAIR=(8,9)
OPENING=20
KEY=284


def inputs(pair):
    return [1<<v for v in vertices(DOMAIN)]+[sum(1<<v for v in pair),sum(1<<v for v in TIPS)]


def encoding(op,a,b):
    require(op in ('AND','OR') and 0<=a<64 and 0<=b<64,'Invalid posted gate')
    return a+64*b+4096*(op=='OR')


def evaluate(initial,gates):
    wires=list(initial)
    for op,a,b in gates:
        require(op in ('AND','OR') and 0<=a<len(wires) and 0<=b<len(wires),'Unavailable operand')
        wires.append(wires[a]&wires[b] if op=='AND' else wires[a]|wires[b])
    return wires[-1]


def relabelings():
    result={}
    for pair in combinations(TIPS,2):
        single=next(v for v in TIPS if v not in pair)
        candidates=[p for _,p in GROUP if {p[v] for v in pair}=={0,1} and p[single]==3 and p[CENTER]==7]
        require(candidates,'No posted opening for the neighbor pair')
        result[pair]=min(candidates)
    return result


def lift(local,pair=PAIR):
    ports=inputs(pair)
    active=vertices(DOMAIN)
    rows=sample(MASK,DOMAIN)
    observed=rows['positive_rows']+rows['negative_rows']
    require(evaluate([column(s,observed) for s in ports],local)==(1<<18)-1,'Wrong local signed output')
    # Check completeness of the signed rows using actual induced assignments.
    assignments=[sum(1<<v for i,v in enumerate(active) if (r>>i)&1) for r in range(1<<len(active))]
    truth=sum(1<<i for i,row in enumerate(assignments) if any((row&e)==e for e in rows['positive_rows']))
    require(evaluate([column(s,assignments) for s in ports],local)==truth,'Wrong local truth table')
    perm=relabelings()[tuple(sorted(pair))]
    index=[perm[v] for v in active]+[14,15]
    prefix=[['OR',0,1],['OR',3,14]]
    require(KEY//225==1 and (KEY%225)//15==3 and KEY%15==14,'Incorrect prescribed opening')
    gates=list(prefix)
    for op,a,b in local:
        require(0<=a<len(index) and 0<=b<len(index),'Invalid local instruction')
        gates.append([op,index[a],index[b]])
        index.append(13+len(gates))
    last=index[-1]
    gates.append(['AND',perm[CENTER],15])
    gates.append(['OR',last,13+len(gates)])
    full=sample(ALL,(1<<14)-1)
    tests=full['positive_rows']+full['negative_rows']
    packed=evaluate([column(1<<v,tests) for v in range(14)],gates)
    require(packed==(1<<21)-1,'Wrong posted word')
    assignments=range(1<<14)
    expected=sum(1<<r for r in assignments if any((r&e)==e for e in full['positive_rows']))
    require(evaluate([column(1<<v,assignments) for v in range(14)],gates)==expected,'Wrong full truth table')
    tail=[encoding(*g) for g in gates[2:]]
    require(len(tail)==len(local)+2 and len(gates)==len(local)+4,'Wrong lifted gate count')
    return dict(opening=OPENING,key=KEY,operations=['OR','OR'],center=perm[CENTER],neighbor_pair=list(pair),
                permutation=list(perm),inputs=ports,local=local,local_gates=len(local),
                local_assignments=1<<len(active),gates=gates,gate_count=len(gates),
                tail=tail,tail_length=len(tail),word=packed,full_assignments=1<<14,
                fits_posted_gate_budget=len(tail)<=24)


def example(pair=PAIR):
    control=star_control(MASK,DOMAIN,23)
    old=sample(MASK,DOMAIN)['signals']
    new=inputs(pair)
    def wire(i):
        return new.index(old[i]) if i<len(old) else len(new)+i-len(old)
    return [[op,wire(a),wire(b)] for op,a,b in control['gates']]


def row_source():
    perm=relabelings()[PAIR]
    inv=tuple(perm.index(v) for v in range(14))
    g=sample(ALL,16383)
    s=sample(MASK,DOMAIN)
    pos=s['positive_rows']
    neg=s['negative_rows']
    cols=[column((1<<inv[v])&DOMAIN,pos+neg) for v in range(14)]
    cols.extend([column(768,pos+neg),column(2816,pos+neg)])
    pos_links=[pos.index(r) if r in pos else 0 for x in g['positive_rows'] for r in [moved(x,inv)]]
    neg_links=[18+next(i for i,n in enumerate(neg) if r&~n==0) for x in g['negative_rows'] for r in [moved(x,inv)&DOMAIN]]
    return '''import WordTransport132

namespace Checkpoint132.Opening
open Checkpoint122.Posted Checkpoint132.Word
open PEqualNP.Outside.L_meta_3008_aux (nums)

def base := ((codes 20 true true []).foldl wordStep nums)
def overlay := base.getD 7 0 &&& base.getD 15 0
def localBase : List ℕ := '''+numbers(cols)+'''
def posLink : List ℕ := '''+numbers(pos_links)+'''
def negLink : List ℕ := '''+numbers(neg_links)+'''

theorem dimensions : base.length=16 ∧ localBase.length=16 ∧ overlay<2^58 := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem positiveLinks : ∀ i : Fin 21,overlay.testBit i.val=true ∨
    (posLink.getD i.val 0<18 ∧ ∀ v : Fin 16,v.val≠7 →
     BitLE (posLink.getD i.val 0) i.val (localBase.getD v.val 0) (base.getD v.val 0)) := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem negativeLinks : ∀ j : Fin 37,overlay.testBit (21+j.val)=false ∧
    18≤negLink.getD j.val 0 ∧ ∀ v : Fin 16,v.val≠7 →
    BitLE (21+j.val) (negLink.getD j.val 0) (base.getD v.val 0) (localBase.getD v.val 0) := by decide +kernel

theorem boundedBase : ∀ v : Fin 16,base.getD v.val 0<2^58 := by decide +kernel

#print axioms dimensions
#print axioms positiveLinks
#print axioms negativeLinks
#print axioms boundedBase
end Checkpoint132.Opening
'''


def lean_source(control):
    tail='['+','.join(map(str,control['tail']))+']'
    return '''import OpeningLift132

namespace Checkpoint132.Completion
open Checkpoint122.Posted

def tail : List (Fin 8192) := '''+tail+'''

/-- The explicit prescribed-opening circuit attains the posted output with 25 tail gates. -/
theorem control : key 20=284 ∧ tail.length=25 ∧ (codes 20 true true tail).length=27 ∧
    output (codes 20 true true tail)=2097151 := by decide +kernel

def localOps := tail.take 23

theorem localControl : localOps.length=23 ∧
    Checkpoint132.Opening.result Checkpoint132.Opening.localBase (localOps.map Fin.val)=262143 ∧
    (localOps.map Fin.val).all (fun q => decide (q%64≠7 ∧ q/64%64≠7))=true := by decide +kernel

#print axioms control
#print axioms localControl
end Checkpoint132.Completion
'''


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='regenerate the published 27-gate control')
    parser.add_argument('--circuit',type=Path,help='JSON list of [AND/OR,left,right] with the output last')
    parser.add_argument('--pair',choices=['8,9','8,11','9,11'],default='8,9')
    args=parser.parse_args()
    pair=tuple(map(int,args.pair.split(',')))
    if args.circuit:
        print(json.dumps(lift(json.loads(args.circuit.read_text()),pair),indent=1))
        return
    controls=[lift(example(p),p) for p in combinations(TIPS,2)]
    data=controls[0]
    require(all(x['gate_count']==27 and x['tail_length']==25 for x in controls),'Wrong positive control')
    data['all_pair_placements']=[dict(pair=x['neighbor_pair'],permutation=x['permutation']) for x in controls]
    for location,content in [(HERE/'completion.json',json.dumps(data,indent=1)+'\n'),
                             (HERE/'src'/'OpeningRows132.lean',row_source()),
                             (HERE/'src'/'OpeningControl132.lean',lean_source(data))]:
        if args.write:
            location.write_text(content)
        else:
            require(location.read_text()==content,'Incorrect opening control')
    print('Opening 20 gives word 2097151 at 27 gates for each of the three pair choices.')


if __name__=='__main__':
    main()
