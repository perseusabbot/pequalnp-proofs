"""Reconstruct the boundary screens and the three star-circuit controls."""
import argparse
import json
from itertools import combinations
from geometry131 import ALL, GROUP, HERE, column, require, sample, serial_cases
from transport import EDGES
from tables import numbers, screen

CONTROL_CASES = [(128895,11679,16),(32767,15775,18),(128895,12223,20)]


def star_control(mask, vertices, gate_count):
    order = [v for v in range(14) if vertices >> v & 1]
    r = sample(mask,vertices)
    edges = [(a,b) for a,b in EDGES if (1 << a | 1 << b) in r['positive_rows']]
    centers = next(c for k in range(1,len(order)+1) for c in combinations(order,k)
                   if all(a in c or b in c for a,b in edges))
    neighbors = {c:[] for c in centers}
    for a,b in edges:
        c = a if a in centers else b
        neighbors[c].append(b if c==a else a)
    def pack(s):
        return sum(1 << i for i,v in enumerate(order) if s >> v & 1)
    columns = [pack(s) for s in r['signals']]
    pairs = [pack(p) for p in r['positive_rows']]
    gates = []
    def add(op,a,b):
        gates.append([op,a,b])
        return len(columns) + len(gates) - 1
    def fold_or(wires):
        head,*tail = wires
        for w in tail:
            head = add('OR',head,w)
        return head
    def port(v):
        return r['signals'].index(1 << v)
    stars = [add('AND',port(c),fold_or([port(v) for v in neighbors[c]])) for c in centers]
    last = fold_or(stars)
    require(last==len(columns)+gate_count-1 and len(gates)==gate_count, 'Wrong star gate count')
    for row in range(1 << len(order)):
        wires = [bool(row & s) for s in columns]
        for op,a,b in gates:
            wires.append((wires[a] or wires[b]) if op=='OR' else (wires[a] and wires[b]))
        require(wires[-1]==any(row&p==p for p in pairs),'Upper control fails')
    return dict(mask=mask,vertices=vertices,vertex_order=order,columns=columns,edges=pairs,gates=gates,
                upper=len(gates),assignments=1 << len(order))


def controls():
    return [star_control(*case) for case in CONTROL_CASES]


def screens():
    rows = []
    for job in serial_cases():
        m,t = job['mask'],job['vertices']
        c = sample(m,t)
        if job['cap'] == c['gate_cap']:
            rows.append(screen(m,t,[(1 << v) & t for v in range(14)],c))
    return '''import ProjectedScreen

namespace Checkpoint131.Heawood
open Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open Checkpoint128.Heawood Checkpoint129.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def boundaryTests : List Screen := [
''' + ',\n'.join(rows) + ''']

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem boundaryValid {c : Screen} (listed : c∈boundaryTests) : ValidScreen c := by
  have all : boundaryTests.all (fun r => decide (ValidScreen r))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ listed)

theorem boundaryNecessary (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z)
    (short : ops.length≤26) {c : Screen} (listed : c∈boundaryTests)
    (eq : lost ((run 14 ops).wires.getD out default)=Checkpoint127.Heawood.decoded c.shape.mask) :
    ∃ book : List (Binary.Tree {m : ℕ // m∈c.signals}), ∃ t, Binary.Built book ∧ Binary.Ready book t ∧
      book.length≤c.cap ∧
      (∀ n∈c.positives,t.eval (fun m => (m.val &&& n)!=0)) ∧
      (∀ n∈c.negatives,¬t.eval (fun m => (m.val &&& n)!=0)) :=
  projectedScreenNecessary ops out spec short (boundaryValid listed) eq

#print axioms boundaryValid
#print axioms boundaryNecessary
end Checkpoint131.Heawood
'''


def full_rows():
    root = sample(ALL,16383)
    p,n = root['positive_rows'],root['negative_rows']
    cols = [column(1<<v,p+n) for v in range(14)]
    return '''import ProgramFloor

namespace Checkpoint131.Full
open Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Heawood
open Checkpoint130.Cut Checkpoint130.Heawood PEqualNP.Outside.L_meta_3004_aux.Controls

def positives : List ℕ := ''' + numbers(p) + '''
def negatives : List ℕ := ''' + numbers(n) + '''
def row (r : ℕ) (v : V) : Bool := r.testBit v.val

theorem rowSigns :
    (∀ r∈positives, edgeOn (row r)=true) ∧ (∀ r∈negatives, edgeOn (row r)=false) := by
  decide +kernel

def signature (v : V) : ℕ :=
  ((positives++negatives).zipIdx.map fun ⟨r,i⟩ => if row r v then 2^i else 0).sum

theorem inputColumns : (List.ofFn signature) = ''' + numbers(cols) + ''' := by decide +kernel

def Holds (e : Binary.Tree V) : Prop :=
  (∀ r∈positives,e.eval (fun v => row r v=true)) ∧ ∀ r∈negatives,¬e.eval (fun v => row r v=true)

theorem programFromRows (k : ℕ)
    (floor : ∀ gs : List (Binary.Tree V), ∀ e, Binary.Built gs → Binary.Ready gs e → Holds e → k≤gs.length)
    (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) : k≤ops.length := by
  obtain ⟨gs,e,hb,hr,hc,truth⟩ := vertexProgram ops out spec
  apply Nat.le_trans (floor gs e hb hr ?_) hc
  exact ⟨fun r h => (truth (row r)).mpr ((edgeOnCorrect _).mp (rowSigns.1 r h)),
    fun r h accepted => Bool.false_ne_true ((rowSigns.2 r h).symm.trans
      ((edgeOnCorrect _).mpr ((truth (row r)).mp accepted)))⟩

theorem postedTwentyFour
    (floor : ∀ gs : List (Binary.Tree V), ∀ e, Binary.Built gs → Binary.Ready gs e → Holds e → 24≤gs.length)
    (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (h : Checkpoint122.Posted.Witness i f g tail) : 22≤tail.length := by
  let qs := Checkpoint122.Posted.codes i f g tail
  have size := programFromRows 24 floor (qs.map Checkpoint122.Posted.decode) (13+qs.length)
    (Checkpoint122.Posted.semantics _ h.2)
  simp only [List.length_map,qs,Checkpoint122.Posted.codes,List.length_cons] at size
  omega

#print axioms rowSigns
#print axioms inputColumns
#print axioms programFromRows
#print axioms postedTwentyFour
end Checkpoint131.Full
'''


def deletion_data():
    d = sample(ALL,16319)
    embeddings = []
    for x in range(14):
        perm = next(p for _,p in GROUP if p[x]==6)
        embeddings.append([0 if v==6 else 1<<v for v in perm])
    return '''import TwentyTwo

namespace Checkpoint131.Deletion
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def ports : List ℕ := ''' + numbers(d['signals']) + '''
def posRows : List ℕ := ''' + numbers(d['positive_rows']) + '''
def negRows : List ℕ := ''' + numbers(d['negative_rows']) + '''
def placements : List (List ℕ) := [
''' + ',\n'.join('  '+numbers(v) for v in embeddings) + ''']

def Legal (q : List ℕ) : Prop := (∀ v : V,code q v∈0::ports) ∧
  (∀ r∈posRows,edgeOn (liftRow q r)=true) ∧ (∀ r∈negRows,edgeOn (liftRow q r)=false)
instance (q) : Decidable (Legal q) := by unfold Legal; infer_instance

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem legalPlacement {q} (h : q∈placements) : Legal q := by
  have all : placements.all (fun r => decide (Legal r))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ h)

theorem deletes : ∀ x : V,∃ q∈placements,code q x=0 := by decide +kernel

def low (op : Bool) (u y v : V) := decide (v=u) || (op && decide (v=y))
def high (op : Bool) (u x y v : V) := decide (v=x) || low op u y v

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem witness : ∀ x y : V,x≠y → ∀ op : Bool,∃ u : V,edgeOn (high op u x y)=true ∧
    edgeOn (low op u y)=false ∧ high op u x y y=op ∧ low op u y y=op := by decide +kernel

#print axioms legalPlacement
#print axioms deletes
#print axioms witness
end Checkpoint131.Deletion
'''


def upper_tables():
    text = 'import ControlSemantics\n\nnamespace Checkpoint131.Upper\nopen Checkpoint129.Controls\n\n'
    for i,c in enumerate(controls()):
        gates = numbers([f'({str(op=="OR").lower()},{a},{b})' for op,a,b in c['gates']])
        size = c['assignments']
        theorem = f"control{c['mask']}_{c['vertices']}"
        text += f"""def columns{i} : List ℕ := {numbers(c['columns'])}
def edges{i} : List ℕ := {numbers(c['edges'])}
def gates{i} : List Gate := {gates}

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows{i} (b : ℕ) (h : b<{size//32}) :
    (List.range 32).all (fun n => decide (correct columns{i} edges{i} gates{i} (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem {theorem} : gates{i}.length={c['upper']} ∧
    (∀ p∈gates{i}.zipIdx,p.1.2.1<columns{i}.length+p.2 ∧ p.1.2.2<columns{i}.length+p.2) ∧
    ∀ r : Fin {size}, correct columns{i} edges{i} gates{i} r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows{i} (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms {theorem}

"""
    return text+'end Checkpoint131.Upper\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    write = parser.parse_args().write
    files = [(HERE/'src'/'DeletionData.lean',deletion_data()),(HERE/'src'/'SurvivingScreens.lean',screens()),(HERE/'src'/'FullRowFloor.lean',full_rows()),(HERE/'src'/'LocalStars.lean',upper_tables()),
             (HERE/'controls.json',json.dumps(controls(),indent=1)+'\n')]
    for path, content in files:
        if write:
            path.write_text(content)
        else:
            require(path.read_text()==content,'Mismatch in '+path.name)
    print('Reconstructed the boundary screens and verified all 7,168 control assignments.')


if __name__=='__main__':
    main()
