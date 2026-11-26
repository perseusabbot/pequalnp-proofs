"""Generate the Lean compatibility tables and the pivot choices in the finite search trees."""
import argparse
from pathlib import Path
from geometry import HERE, ROWS, axes, bits, boundary_points, maximal_rectangles, require

MODULES = {'triangle3': 'TriangleBoundary', 'homology3': 'HomologyBoundary', 'five': 'FiveBoundary'}


def data(name, maximal):
    p, q, h = axes(name)
    slots = 2 if h == 5 else 3
    cells = boundary_points(name, maximal)
    orbits = []
    for x, y in cells:
        orbit = []
        for _ in range(h):
            orbit.append((x,y))
            x, y = p[x], q[y]
        orbits.append(orbit)
    n = len(cells)
    lanes = slots*h
    pattern = []
    guards = []
    for i, orbit in enumerate(orbits):
        x, y = orbit[0]
        pattern.append(sum(1 << (j*h+b) for j, other in enumerate(orbits)
                           for b, (r,c) in enumerate(other) if ROWS[x] >> c & ROWS[r] >> y & 1))
        for label in range(lanes):
            x, y = orbit[label % h]
            guards.append(sum(1 << (j*lanes+t) for j, other in enumerate(orbits)
                              for t in range(lanes) if t//h != label//h
                              or ROWS[x] >> other[t%h][1] & ROWS[other[t%h][0]] >> y & 1))
    full = (1 << (lanes*n))-1
    records = []
    def visit(state, remaining, used):
        require(remaining != 0, 'Compatible assignment found')
        allowed = (1 << (h*used))-1
        if used < slots:
            allowed |= 1 << (h*used)
        _, i, domain = min((d.bit_count(), i, d) for i in bits(remaining)
                           for d in [(state >> (i*lanes)) & allowed])
        children = [0]*lanes
        for t in bits(domain):
            children[t] = visit(state & guards[i*lanes+t], remaining ^ (1 << i), max(used, t//h+1))
        records.append((i,children,state,used))
        return len(records)-1
    root = visit(full, (1 << n)-1, 0)
    width = max(1,root.bit_length())
    tree = [i + 64*sum(k << (t*width) for t,k in enumerate(kids)) for i,kids,_,_ in records]
    return p,q,h,slots,cells,pattern,guards,width,tree,[w*4+u for _,_,w,u in records]


def literal(values):
    return '#['+', '.join(map(str,values))+']'


def table(name, values):
    lines=[]
    for i in range(0,len(values),96):
        lines.append(f'def {name}{i//96} : Array ℕ := '+literal(values[i:i+96]))
    lines.append(f'def {name}Blocks : Array (Array ℕ) := '+literal([name+str(i//96) for i in range(0,len(values),96)]))
    lines.append(f'def {name} (i : ℕ) : ℕ := (({name}Blocks).getD (i/96) #[]).getD (i%96) 0')
    return '\n'.join(lines)


def scans(stem, fn, count, chunk):
    parts=[]
    blocks=[]
    for j in range(0,count,chunk):
        w=min(count-j,chunk)
        name=f'{stem}Part{j}'
        parts.append(f'private theorem {name} : ValidOn ({fn}) {j} {j+w} := scanned _ {j} {w} (by decide +kernel)')
        blocks.append(name)
    while len(blocks)>1:
        blocks=[f'(combine {blocks[i]} {blocks[i+1]})' if i+1<len(blocks) else blocks[i]
                for i in range(0,len(blocks),2)]
    parts.append(f'private theorem {stem} : ValidOn ({fn}) 0 {count} := '+blocks[0])
    return '\n'.join(parts)


def source(name, maximal):
    p,q,h,s,cells,pat,guards,width,tree,states=data(name,maximal)
    n=len(cells)
    arrays='\n'.join([table('guardWord',guards),table('tree',tree),table('spares',states)])
    mod=MODULES[name]
    coords=literal([f'({x}, {y})' for x,y in cells])
    return f'''import OrbitGeometry

namespace Checkpoint135.{mod}
open PEqualNP.Outside.L_meta_9338 (V Box bit legal hit ValidOn scanned combine)
set_option maxHeartbeats 0
set_option maxRecDepth 12000

def rows : Array V := {literal(p)}
def columns : Array V := {literal(q)}
def rotation : Rotation := ⟨fun x => rows.getD x.val 0, fun y => columns.getD y.val 0⟩
def representatives : Array (V × V) := {coords}
def point (i : Fin {n}) := representatives.getD i.val (0,0)
def patterns : Array ℕ := {literal(pat)}
def allowed (i j : Fin {n}) (d : Fin {h}) := (patterns.getD i.val 0).testBit (j.val*{h}+d.val)
{arrays}
def mask (i : Fin {n}) (c : Fin {s}) (a : Fin {h}) := guardWord (address i c a)
def guardCheck := guardTest allowed mask
{scans('masksValid','guardCheck',n,1)}
def search : Search {n} {s} {h} where
  pattern := allowed
  guard := mask
  correct := checkedGuards allowed mask (fun k hk => masksValid k (Nat.zero_le _) hk)
  pivot := fun v => Fin.ofNat {n} (tree v % 64)
  child := fun v c a => (tree v >>> (6+{width}*(c.val*{h}+a.val))) % {1<<width}
def states : Search.Tree := ⟨fun i => spares i / 4,fun i => spares i % 4⟩
{scans('nodesValid','search.checkNode states',len(tree),48)}

/-- Each search node selects a cell. All viable slot and phase choices below it are checked. -/
theorem exhausted : ∀ f, ¬search.compatible f := by
  have start : states.domain {len(tree)-1}={(1<<(n*s*h))-1} ∧ states.used {len(tree)-1}=0 := by decide +kernel
  have spare : Search.free (n:={n}) (s:={s}) (p:={h}) (states.domain {len(tree)-1}) (states.used {len(tree)-1}) := by
    rw [start.1,start.2]; unfold Search.free; decide +kernel
  intro f good
  exact search.sound states {len(tree)} (fun v hv => nodesValid v (Nat.zero_le _) hv) {len(tree)-1} (by decide) spare f good
    (fun i => spare i _ _ (start.2 ▸ Nat.zero_le _))

/-- Even with arbitrarily many invariant legal rectangles, these moving slots cannot cover the board. -/
theorem movingLower (family : Fin {s} → Box) (law : ∀t, legal (family t))
    (cover : ∀ x y : V, bit x y=false →
      (∃ b, legal b ∧ rotation.stable b ∧ hit b x y) ∨ ∃t,rotation.meets {h} (family t) x y) : False := by
  apply rotation.boundary search point (by decide +kernel) (by decide +kernel) _ exhausted family law cover
  decide +kernel

#print axioms exhausted
#print axioms movingLower
end Checkpoint135.{mod}
'''


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,help='Write sources here. By default check existing bytes.')
    args=parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True,exist_ok=True)
    maximal=maximal_rectangles()
    for name,mod in MODULES.items():
        raw=source(name,maximal)
        path=(args.output or HERE/'src')/(mod+'.lean')
        if args.output:
            path.write_text(raw)
        else:
            require(path.read_text()==raw,f'Certificate differs in {mod}')
        print(mod)

if __name__=='__main__':
    main()
