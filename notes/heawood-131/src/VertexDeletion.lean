import DeletionData
import ProgramFloor

namespace Checkpoint131.Deletion
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Prune Checkpoint130.Heawood
open Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

abbrev Input := {w : ℕ // w∈ports}
abbrev On := {w : ℕ // w∈posRows}
abbrev Off := {w : ℕ // w∈negRows}
def on (r : On) (a : Input) : Prop := (r.val &&& a.val)!=0
def off (r : Off) (a : Input) : Prop := (r.val &&& a.val)!=0

private theorem noSingle (v : V) : ¬Fits positiveValue negativeValue (.leaf v) := by
  have single : ∀ w : V, edgeOn (fun u => decide (u=w))=false := by decide +kernel
  have no : ¬predicate (fun u => decide (u=v)) := fun h =>
    Bool.false_ne_true ((single v).symm.trans ((edgeOnCorrect _).mpr h))
  intro h
  exact h.2 ⟨_,no⟩ (by simp [Binary.Tree.eval,negativeValue])

/-- The first operand of a distinct-operand gate is still used after cutting that gate. -/
theorem oldOperand (op : Bool) {x y : V} (ne : x≠y) {t : Binary.Tree (Option V)}
    (ok : Fits (fun z => extend op x y (positiveValue z)) (fun z => extend op x y (negativeValue z)) t) :
    some x∈t.vars := by
  obtain ⟨u,yes,no,hy,ly⟩ := witness x y ne op
  let a : Yes := ⟨high op u x y,(edgeOnCorrect _).mp yes⟩
  let b : No := ⟨low op u y,fun h => Bool.false_ne_true (no.symm.trans ((edgeOnCorrect _).mpr h))⟩
  apply mandatory ok _ a b
  rintro (_|v) different
  · cases op <;> simp [extend,positiveValue,negativeValue,a,b,hy,ly]
  · change high op u x y v=true → low op u y v=true
    have vx : v≠x := fun eq => different (congrArg some eq)
    simp [high,vx]

private def vertex (q : List ℕ) (v : V) : Value Input :=
  if h : code q v∈ports then .wire ⟨_,h⟩ else .bit false

private def translate (q : List ℕ) (op : Bool) (y : V) : Option V→Value Input
  | some v => vertex q v
  | none => if op then vertex q y else .bit false

private theorem atVertex (q : List ℕ) (valid : Legal q) (v : V) (r : ℕ) :
    (vertex q v).truth (fun w => (r &&& w.val)!=0) ↔ liftRow q r v=true := by
  by_cases h : code q v∈ports
  · simp [vertex,h,Value.truth,liftRow,Nat.and_comm]
  · have zero := (List.mem_cons.mp (valid.1 v)).resolve_right h
    have missing : 0∉ports := by decide +kernel
    simp [vertex,zero,missing,Value.truth,liftRow]

private theorem agrees (q : List ℕ) (valid : Legal q) (op : Bool) (x y : V) (deleted : code q x=0)
    (a : Option V) (r : ℕ) :
    (translate q op y a).truth (fun w => (r &&& w.val)!=0) ↔
      extend op x y (fun v => liftRow q r v=true) a := by
  cases a with
  | some v => exact atVertex q valid v r
  | none =>
    have zero : liftRow q r x=false := by simp [liftRow,deleted]
    cases op
    · simp [translate,Value.truth,extend,zero]
    · simpa [translate,extend,zero] using atVertex q valid y r

private theorem afterCut (op : Bool) {x y : V} (ne : x≠y) {gs : List (Binary.Tree (Option V))}
    {t : Binary.Tree (Option V)} (hb : Built gs) (hr : Ready gs t) (fresh : none∈t.vars)
    (ok : Fits (fun z => extend op x y (positiveValue z)) (fun z => extend op x y (negativeValue z)) t) :
    ∃ qs : List (Binary.Tree Input), ∃ out, Built qs ∧ Ready qs out ∧ Fits on off out ∧
      qs.length+(if op then 1 else 2)≤gs.length := by
  obtain ⟨q,hq,dead⟩ := deletes x
  have valid := legalPlacement hq
  let px (r : On) : Yes := ⟨liftRow q r.val,(edgeOnCorrect _).mp (valid.2.1 _ r.property)⟩
  let nx (r : Off) : No := ⟨liftRow q r.val,fun h => Bool.false_ne_true
    ((valid.2.2 _ r.property).symm.trans ((edgeOnCorrect _).mpr h))⟩
  have hi (r : On) (a) : extend op x y (positiveValue (px r)) a → (translate q op y a).truth (on r) :=
    (agrees q valid op x y dead a r.val).mpr
  have lo (r : Off) (a) : (translate q op y a).truth (off r) → extend op x y (negativeValue (nx r)) a :=
    (agrees q valid op x y dead a r.val).mp
  let fixed : Finset (Option V) := if op then {some x} else {none,some x}
  have old : some x∈t.vars ∧ (translate q op y (some x)).port=none := by
    have missing : 0∉ports := by decide +kernel
    exact ⟨oldOperand op ne ok,by simp [translate,vertex,dead,missing,Value.port]⟩
  have needed (a) (h : a∈fixed) : a∈t.vars ∧ (translate q op y a).port=none := by
    cases op
    · simp only [fixed,Bool.false_eq_true,ite_false,mem_insert,mem_singleton] at h
      rcases h with rfl|rfl
      · exact ⟨fresh,rfl⟩
      · exact old
    · have ax : a=some x := by simpa [fixed] using h
      exact ax ▸ old
  obtain ⟨qs,out,bq,rq,fit,price⟩ := signedProjection hb hr ok (translate q op y) on off px nx hi lo
    ⟨posRows.headD 0,by decide +kernel⟩ ⟨negRows.headD 0,by decide +kernel⟩ fixed needed
  have count : fixed.card=(if op then 1 else 2) := by cases op <;> simp [fixed]
  exact ⟨qs,out,bq,rq,fit,count ▸ price⟩

/-- After cutting the first gate, delete its first operand. The fresh wire becomes
zero for AND and the other operand for OR. The two savings are distinct. -/
theorem twoGateReduction {book : List (Binary.Tree V)} (built : Built book) {e : Binary.Tree V}
    (ready : Ready book e) (truth : ∀ z : V→Bool,e.eval (fun v => z v=true) ↔ predicate z) :
    ∃ gs : List (Binary.Tree Input), ∃ t, Built gs ∧ Ready gs t ∧ Fits on off t ∧ gs.length+2≤book.length := by
  have root : Fits positiveValue negativeValue e :=
    ⟨fun z => (truth z.val).mpr z.property,fun z h => z.property ((truth z.val).mp h)⟩
  obtain ⟨op,x,y,ne,gs,t,hb,hr,size,fresh,ok⟩ := firstDistinct noSingle built ready root
  obtain ⟨qs,out,bq,rq,fit,price⟩ := afterCut op ne hb hr fresh ok
  exact ⟨qs,out,bq,rq,fit,by cases op <;> simp_all <;> omega⟩

/-- An occurring AND on two distinct vertices costs a third gate under deletion.
The AND output and its deleted operand are two different live constant labels. -/
theorem bottomAndReduction {book : List (Binary.Tree V)} (built : Built book) {e : Binary.Tree V}
    (ready : Ready book e) (truth : ∀ z : V→Bool,e.eval (fun v => z v=true) ↔ predicate z)
    {x y : V} (ne : x≠y) (used : Binary.Tree.gate false (.leaf x) (.leaf y)∈Checkpoint126.Cherry.nodes e) :
    ∃ gs : List (Binary.Tree Input), ∃ t, Built gs ∧ Ready gs t ∧ Fits on off t ∧ gs.length+3≤book.length := by
  have root : Fits positiveValue negativeValue e :=
    ⟨fun z => (truth z.val).mpr z.property,fun z h => z.property ((truth z.val).mp h)⟩
  obtain ⟨gs,t,hb,hr,size,fresh,ok⟩ := split built ready root used
  obtain ⟨qs,out,bq,rq,fit,price⟩ := afterCut false ne hb hr fresh ok
  simp only [Bool.false_eq_true,ite_false] at price
  exact ⟨qs,out,bq,rq,fit,by omega⟩

theorem bottomAndTwentyFive (floor : ∀ gs : List (Binary.Tree Input), ∀ t,
    Built gs → Ready gs t → Fits on off t → 22≤gs.length)
    {book : List (Binary.Tree V)} (built : Built book) {e : Binary.Tree V} (ready : Ready book e)
    (truth : ∀ z : V→Bool,e.eval (fun v => z v=true) ↔ predicate z)
    {x y : V} (ne : x≠y) (used : Binary.Tree.gate false (.leaf x) (.leaf y)∈Checkpoint126.Cherry.nodes e) :
    25≤book.length := by
  obtain ⟨gs,t,hb,hr,ok,price⟩ := bottomAndReduction built ready truth ne used
  have localBound := floor gs t hb hr ok
  omega

theorem programFromDeletion (k : ℕ) (floor : ∀ gs : List (Binary.Tree Input), ∀ e,
    Built gs → Ready gs e → Fits on off e → k≤gs.length) (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) : k+2≤ops.length := by
  obtain ⟨book,e,hb,hr,cap,truth⟩ := vertexProgram ops out spec
  obtain ⟨qs,t,bq,rq,ok,n⟩ := twoGateReduction hb hr truth
  have localBound := floor qs t bq rq ok
  omega

#print axioms oldOperand
#print axioms twoGateReduction
#print axioms bottomAndReduction
#print axioms bottomAndTwentyFive
#print axioms programFromDeletion
end Checkpoint131.Deletion
