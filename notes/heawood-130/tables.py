"""Reconstruct the Lean screen data and the small covering family of vertex restrictions."""
import argparse
from itertools import combinations

from transport import DIRECT, HERE, disjoint_matching, fano_actions, instance, moved, read, source_screens


def numbers(xs):
    return '[' + ','.join(map(str, xs)) + ']'


def screen(mask, t, code, source):
    fields = [f'⟨{mask},{t},{numbers(code)}⟩', str(source['gate_cap']), numbers(disjoint_matching(mask))]
    fields.extend(numbers(source[k]) for k in ('signals', 'positive_rows', 'negative_rows'))
    return '  ⟨' + ','.join(fields) + '⟩'


def screens():
    lines = []
    for mask, t in DIRECT:
        c = instance(mask, t)
        lines.append(screen(mask, t, [(1 << v) & t for v in range(14)], c))
    c = next(c for c in source_screens() if c['representative'] == 32751)
    row = next(r for layer in read(HERE/'frontier.json')['layers'] for r in layer['class_bounds']
               if r['representative'] == 121855)
    if row['source'] != c['representative']:
        raise ValueError('Wrong inherited screen')
    t = row['sample_vertices']
    code = [(1 << row['permutation'].index(v)) if t >> v & 1 else 0 for v in range(14)]
    lines.append(screen(121855, t, code, c))
    return '''import ProjectedScreen

namespace Checkpoint130.Heawood
open Checkpoint128.Heawood Checkpoint129.Heawood

def fifteen : List Screen := [
''' + ',\n'.join(lines) + ''']

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem fifteenValid {c : Screen} (listed : c∈fifteen) : ValidScreen c := by
  have all : fifteen.all (fun r => decide (ValidScreen r))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ listed)

#print axioms fifteenValid
end Checkpoint130.Heawood
'''


def embeddings():
    sample = next(c for c in source_screens() if c['representative'] == 32751)
    t = sample['sample_vertices']
    choices = {}
    for _, p in fano_actions()[0]:
        d = ((1 << 14)-1) ^ moved(t, p)
        code = tuple(1 << p.index(v) if not d >> v & 1 else 0 for v in range(14))
        choices.setdefault(d, code)
    uncovered = set(combinations(range(14), 2))
    chosen = []
    while uncovered:
        d = min(choices, key=lambda d: (-sum(d >> x & d >> y & 1 for x, y in uncovered), d))
        removed = {(x, y) for x, y in uncovered if d >> x & d >> y & 1}
        if not removed:
            raise ValueError('Incomplete operand-pair cover')
        chosen.append(choices[d])
        uncovered -= removed
    return '''import ProjectedBlock14
import EdgeRows

namespace Checkpoint130.Heawood
open Finset Checkpoint128.Heawood Checkpoint129.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def five : Screen := ''' + screen(32751, t, [(1 << v) & t for v in range(14)], sample).strip() + '''

theorem sameFive : block14[6]?=some five := by rfl

def embeddings : List (List ℕ) := [
''' + ',\n'.join('  '+numbers(x) for x in chosen) + ''']

def code (q : List ℕ) (v : V) := q.getD v.val 0
def outside (q : List ℕ) := univ.filter fun v : V => code q v=0
def liftRow (q : List ℕ) (r : ℕ) (v : V) : Bool := (code q v &&& r)!=0

local instance (z : V→Bool) : Decidable (predicate z) := rowDec z

def Good (q : List ℕ) : Prop :=
  (outside q).card=4 ∧ (∀ v : V,code q v∈0::five.signals) ∧
  (∀ r∈five.positives,predicate (liftRow q r)) ∧ (∀ r∈five.negatives,¬predicate (liftRow q r))
instance (q) : Decidable (Good q) := by unfold Good; infer_instance

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem goodEmbedding {q : List ℕ} (h : q∈embeddings) : Good q := by
  have all : embeddings.all (fun q => decide (Good q))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ h)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem coverPair : ∀ x y : V,x≠y → ∃ q∈embeddings,code q x=0 ∧ code q y=0 := by decide +kernel

#print axioms goodEmbedding
#print axioms coverPair
end Checkpoint130.Heawood
'''


def upper_controls():
    from controls import circuits
    text = """import ControlSemantics

namespace Checkpoint130.Upper
open Checkpoint129.Controls

"""
    for i,c in enumerate(circuits()):
        gates = numbers([f'({str(op=="OR").lower()},{a},{b})' for op,a,b in c['gates']])
        width = c['assignments']
        text += f"""def columns{i} : List ℕ := {numbers(c['columns'])}
def edges{i} : List ℕ := {numbers(c['edges'])}
def gates{i} : List Gate := {gates}

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows{i} (b : ℕ) (h : b<{width//32}) :
    (List.range 32).all (fun n => decide (correct columns{i} edges{i} gates{i} (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem control{c['mask']} : gates{i}.length={c['minimum']} ∧
    (∀ p∈gates{i}.zipIdx,p.1.2.1<columns{i}.length+p.2 ∧ p.1.2.2<columns{i}.length+p.2) ∧
    ∀ r : Fin {width}, correct columns{i} edges{i} gates{i} r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows{i} (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms control{c['mask']}

"""
    return text+'end Checkpoint130.Upper\n'


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('--write', action='store_true')
    write = args.parse_args().write
    for name, data in [('FifteenScreens.lean', screens()), ('FiveEmbeddings.lean', embeddings()),
                       ('SampleControls.lean', upper_controls())]:
        path = HERE/'src'/name
        if write:
            path.write_text(data)
        elif path.read_text() != data:
            raise ValueError('Lean data differs for '+name)
    print('Verified all five loss tables and the operand-pair cover and all four control circuits.')


if __name__ == '__main__':
    main()
