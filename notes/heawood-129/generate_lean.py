"""Check or regenerate the kernel's concrete projected row tables."""
import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def numbers(xs):
    return '[' + ','.join(map(str, xs)) + ']'


def generate():
    cases = json.loads((HERE/'screens.json').read_text())
    prefix = '''import ProjectedScreen

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

'''
    parts = []
    for i in range(0, len(cases), 7):
        lines = []
        for c in cases[i:i+7]:
            points = c['sample_vertices']
            codes = [(1 << v) if points >> v & 1 else 0 for v in range(14)]
            shape = '⟨' + ','.join(map(str, (c['representative'], points, numbers(codes)))) + '⟩'
            fields = [shape, str(c['gate_cap']), *[numbers(c[key]) for key in ('matching','signals','positive_rows','negative_rows')]]
            lines.append('  ⟨' + ','.join(fields) + '⟩')
        part = i//7
        parts.append(f'block{part}')
        yield f'ProjectedBlock{part}.lean', prefix + f'def block{part} : List Screen := [\n' + ',\n'.join(lines) + ''']

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
''' + f'theorem block{part}Checked : block{part}.all (fun c => decide (ValidScreen c))=true := by decide +kernel\n' + '\nend Checkpoint129.Heawood\n'
    imports = '\n'.join(f'import ProjectedBlock{i}' for i in range(len(parts)))
    proofs = ','.join(s+'Checked' for s in parts)
    yield 'LayerScreens.lean', imports + '''

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def layers : List Screen := ''' + ' ++ '.join(parts) + '''

/-- Each directly searched representative satisfies the geometric
and gate-count hypotheses of the projected circuit theorem. -/
theorem allScreensValid {c : Screen} (h : c∈layers) : ValidScreen c := by
  have all : layers.all (fun r => decide (ValidScreen r))=true := by
    simp only [layers,List.all_append,'''+proofs+''',Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp all _ h)

#print axioms allScreensValid
end Checkpoint129.Heawood
'''


def transport_tables():
    from instances import disjoint_matching
    direct = json.loads((HERE/'screens.json').read_text())
    positions = {q['representative']:i for i,q in enumerate(direct)}
    transfers = json.loads((HERE/'transfers.json').read_text())
    yield 'TransportData.lean', '''import LayerScreens

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def emptyScreen : Screen := ⟨⟨0,0,[]⟩,0,[],[],[],[]⟩

/-- Retain the source test's entire input palette, row specification and cap. -/
def retarget (source : Screen) (shape : Shape) (matching : List (Fin 21)) : Screen :=
  { source with shape := shape, matching := matching }

end Checkpoint129.Heawood
'''
    blocks = []
    for start in range(0,len(transfers),8):
        num = start//8
        name = f'moved{num}'
        blocks.append(name)
        lines = []
        for q in transfers[start:start+8]:
            i = positions[q['source']]
            c = direct[i]
            codes = [0]*14
            for v,w in enumerate(q['permutation']):
                if c['sample_vertices'] >> v & 1:
                    codes[w] = 1 << v
            points = sum(1 << v for v,code in enumerate(codes) if code)
            m = q['representative']
            source = f'(block{i//7}.getD {i%7} emptyScreen)'
            lines.append(f'  retarget {source} ⟨{m},{points},{numbers(codes)}⟩ {numbers(disjoint_matching(m))}')
        yield f'TransportedBlock{num}.lean', '''import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

''' + f'def {name} : List Screen := [\n' + ',\n'.join(lines) + ''']

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
''' + f'theorem {name}Checked : {name}.all (fun c => decide (ValidScreen c))=true := by decide +kernel\n' + '\nend Checkpoint129.Heawood\n'
    yield 'TransportAudit.lean', '\n'.join(f'import TransportedBlock{i}' for i in range(len(blocks))) + '''

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def transported : List Screen := ''' + ' ++ '.join(blocks) + '''

theorem allTransferredValid {c : Screen} (h : c∈transported) : ValidScreen c := by
  have all : transported.all (fun r => decide (ValidScreen r))=true := by
    simp only [transported,List.all_append,'''+','.join(s+'Checked' for s in blocks)+''',Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp all _ h)

#print axioms allTransferredValid
end Checkpoint129.Heawood
'''


def local_controls():
    for ns,filename in [('FourStar','k4.json'),('FiveStar','five_stars.json')]:
        c = json.loads((HERE/filename).read_text())
        gates = numbers([f'({str(op=="OR").lower()},{a},{b})' for op,a,b in c['gates']])
        yield ns+'Control.lean', f'''import ControlSemantics

namespace Checkpoint129.{ns}
open Checkpoint129.Controls

def columns : List ℕ := {numbers(c['signals'])}
def pairs : List ℕ := {numbers(c['edge_words'])}
def gates : List Gate := {gates}

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows (b : ℕ) (h : b<32) :
    (List.range 32).all (fun n => decide (correct columns pairs gates (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem controlWorks : gates.length={len(c['gates'])} ∧
    (∀ p∈gates.zipIdx,p.1.2.1<columns.length+p.2 ∧ p.1.2.2<columns.length+p.2) ∧
    ∀ r : Fin 1024, correct columns pairs gates r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms controlWorks
end Checkpoint129.{ns}
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    for name, content in [*generate(), *transport_tables(), *local_controls()]:
        if args.output:
            args.output.mkdir(parents=True, exist_ok=True)
            (args.output/name).write_text(content)
        elif content != (HERE/'src'/name).read_text():
            raise ValueError('Regenerated source differs for ' + name)


if __name__ == '__main__':
    main()
