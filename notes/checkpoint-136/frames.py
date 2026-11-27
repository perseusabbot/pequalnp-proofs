"""Build the incidence and short permutation-word certificates for the full board group."""
import argparse
from itertools import combinations
from plane import HERE, IDENTITY, LINES_AT, POINTS_ON, common, frame_data, inverse, require, table
from geometry import axes


def listed(xs):
    return '['+','.join(map(str,xs))+']'


def certificates():
    p,q,_=axes('five')
    generators=[bytes([(i+1)%21 for i in range(21)]+[21+(i+1)%21 for i in range(21)]),
                bytes(p+[21+j for j in q]),bytes([2*i%21 for i in range(21)]+[21+(2*i+7)%21 for i in range(21)])]
    steps=[table(g) for g in generators]
    paths={IDENTITY:()}; queue=[IDENTITY]
    for g in queue:
        for j,t in enumerate(steps):
            h=g.translate(t)
            if h not in paths:
                paths[h]=paths[g]+(j,);queue.append(h)
    require(len(queue)==120960,'The three collineations do not generate the expected group')
    seed,allowed,_=frame_data()
    lines=['import FrameCore','', 'namespace Checkpoint136', 'open PEqualNP.Outside.L_meta_9338 (V bit)',
           'set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
           'private def vec (a : List V) (i : V) : V := a.getD i.val 0',
           'private def checkedPerm (p q : V → V) (l : ∀i,q (p i)=i) (r : ∀i,p (q i)=i) : Equiv.Perm V :=',
           '  ⟨p,q,l,r⟩','']
    for n,g in enumerate(generators):
        for side,vs in [('r',g[:21]),('c',bytes(z-21 for z in g[21:]))]:
            lines.append(f'private def {side}{n} : Equiv.Perm V := checkedPerm (vec {listed(vs)}) (vec {listed(inverse(vs))}) (by decide) (by decide)')
        lines.append(f'def generator{n} : Axis := ⟨(r{n},c{n}),by change ∀i j,bit (r{n} i) (c{n} j)=bit i j; decide⟩')
    lines+=['','def baseGroup : Subgroup Axis := Subgroup.closure {generator0,generator1,generator2}',
            'private def generator : Fin 3 → Axis | 0 => generator0 | 1 => generator1 | 2 => generator2',
            'private def word : List (Fin 3) → Axis | [] => 1 | i::w => word w * generator i',
            'private theorem wordMember (w : List (Fin 3)) : word w ∈ baseGroup := by',
            '  induction w with','  | nil => exact baseGroup.one_mem','  | cons i w h =>',
            '    apply baseGroup.mul_mem h','    apply Subgroup.subset_closure',
            '    fin_cases i <;> simp [generator]','']
    def fixedProof(prefix):
        known=set(prefix); out=[]
        def h(v):return ('hr' if v<21 else 'hc')+str(v%21)
        for z in prefix:
            out.append(f'  have {h(z)} : row g.val ({z}:V)={z} := g.property {z} (by decide)')
        while True:
            count=len(known)
            for side,m in [(0,LINES_AT),(1,POINTS_ON)]:
                labels=sorted(i for i in known if i//21==side)
                for a,b in combinations(labels,2):
                    dest=common(a%21,b%21,m)+(1-side)*21
                    if dest in known:continue
                    known.add(dest)
                    fn,shore=('fixedPoint','row') if dest<21 else ('fixedLine','col')
                    out.append(f'  have {h(dest)} : {shore} g.val ({dest%21}:V)={dest%21} := {fn} g.val {h(a)} {h(b)} (by decide) (by decide) (by decide)')
            if len(known)==count:break
        return sorted(known),out
    current=queue
    for k,(a,choices) in enumerate(zip(seed,allowed)):
        prefix=seed[:k][::-1]
        movers={}
        for g in current:
            movers.setdefault(g[a],paths[g])
        require(set(movers)==set(choices),'Wrong stabilizer orbit')
        current=[g for g in current if g[a]==a]
        opts=f'options{k}';prev=listed(prefix)
        lines+=[f'private def {opts} : Finset V := ('+'{'+','.join(map(str,choices))+'} : Finset V)',
                f'private def words{k} : List (List (Fin 3)) := '+listed([listed(movers.get(j,())) for j in range(21)]),
                f'private theorem reachable{k} (v : V) (hv : v∈{opts}) :',
                f'    ∃g : fixing {prev},g.val∈baseGroup ∧ row g.val {a}=v := by',
                f'  have good : ∀i : V, i∈{opts} → (∀x∈({prev}:List V),row (word (words{k}.getD i.val [])) x=x) ∧',
                f'      row (word (words{k}.getD i.val [])) {a}=i := by decide',
                f'  exact ⟨⟨_,(good v hv).1⟩,wordMember _,(good v hv).2⟩',
                f'private theorem upper{k} (g : fixing {prev}) : row g.val {a}∈{opts} := by']
        known,out=fixedProof(prefix);lines+=out
        r=[i for i in known if i<21]; c=[i-21 for i in known if i>=21]
        lines+=[f'  have limited : ∀b : V, compatible {listed(r)} {listed(c)} {a} b → b∈{opts} := by',
                '    unfold compatible','    decide',f'  apply limited _ (imageCompatible g.val {a} ?_ ?_)']
        for vs in (r,c):
            if not vs:lines+=['  · simp'];continue
            lines+=['  · intro z hz','    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz',
                    '    rcases hz with '+' | '.join(['rfl']*len(vs))+(' <;> assumption' if len(vs)>1 else '; assumption')]
        lines+=['']
    prefix=seed[::-1];prev=listed(prefix)
    lines.append(f'private theorem lastIdentity (g : fixing {prev}) : g.val=1 := by')
    known,out=fixedProof(prefix);require(len(known)==42,'Frame did not generate every label')
    lines+=out+['  apply Subtype.ext','  apply Prod.ext',
                '  · apply Equiv.ext; intro i; fin_cases i <;> assumption',
                '  · apply Equiv.ext; intro i; fin_cases i <;> assumption','',
                '/-- The full axis-preserving symmetry group of the posted matrix. -/',
                'theorem collineationCount : Nat.card Axis=120960 := by',
                f'  let : Subsingleton (fixing {prev}) := ⟨fun x y => Subtype.ext ((lastIdentity x).trans (lastIdentity y).symm)⟩',
                '  rw [emptyCard]']
    for k,a in enumerate(seed):
        lines.append(f'  rw [stepCard {listed(seed[:k][::-1])} {a} options{k} upper{k} (fun v h => (reachable{k} v h).imp fun _ q => q.2)]')
    lines+=['  rw [Nat.card_unique]','  decide','',
            '/-- Three previously published axis maps generate every collineation. -/',
            'theorem generatorsComplete : baseGroup=⊤ := by','  apply top_unique','  intro f _',
            '  have enumerate : ∀g : fixing [],g.val∈baseGroup := by']
    for k,a in enumerate(seed):
        lines.append(f'    apply extendMembership (a:={a}) (fun g => reachable{k} _ (upper{k} g))')
    lines+=['    intro g; rw [lastIdentity]; exact baseGroup.one_mem',
            '  exact enumerate ⟨f,by simp [fixing]⟩','',
            'abbrev Dual := {g : Equiv.Perm V × Equiv.Perm V // ∀i j,bit (g.1 j) (g.2 i)=bit i j}',
            'private def reverseAxis : Equiv.Perm V := checkedPerm (vec '+listed([(-i)%21 for i in range(21)])+')',
            '  (vec '+listed([(-i)%21 for i in range(21)])+') (by decide) (by decide)',
            'private theorem reverseBoard : ∀i j,bit (reverseAxis j) (reverseAxis i)=bit i j := by decide',
            'private theorem reverseTwice : ∀i,reverseAxis (reverseAxis i)=i := by decide',
            'def toDual : Axis ≃ Dual where',
            '  toFun g := ⟨(row g*reverseAxis,col g*reverseAxis),fun i j => (g.property _ _).trans (reverseBoard i j)⟩',
            '  invFun g := ⟨(g.val.1*reverseAxis,g.val.2*reverseAxis),fun i j => (g.property (reverseAxis j) (reverseAxis i)).trans (reverseBoard i j)⟩',
            '  left_inv g := by','    apply Subtype.ext; apply Prod.ext <;> apply Equiv.ext <;> intro x <;> simp only [row,col,Equiv.Perm.mul_apply,reverseTwice]',
            '  right_inv g := by','    apply Subtype.ext; apply Prod.ext <;> apply Equiv.ext <;> intro x <;> simp only [row,col,Equiv.Perm.mul_apply,reverseTwice]','',
            '/-- A symmetry either preserves both shores or exchanges them. -/',
            'theorem fullBoardCount : Nat.card (Sum Axis Dual)=241920 := by',
            '  rw [Nat.card_sum,← Nat.card_congr toDual,collineationCount]','',
            '#print axioms collineationCount','#print axioms generatorsComplete','#print axioms fullBoardCount',
            'end Checkpoint136','']
    return '\n'.join(lines)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true')
    args=ap.parse_args()
    source=certificates()
    p=HERE/'src'/'Frames.lean'
    if args.write:p.write_text(source)
    else:require(p.read_text()==source,'Frame certificate differs')
    print('Checked five stabilizer orbits and 42 determined labels.')
