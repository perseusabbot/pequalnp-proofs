import RebuiltPrefix

namespace Checkpoint131.Rebuild
open Checkpoint125 Checkpoint125.Binary Checkpoint130.Prune
variable {B I J : Type}

def available (base : List (Binary.Tree B)) : Value (Binary.Tree B) → Prop
  | .bit _ => True
  | .wire w => Ready base w

def logic (op : Bool) (x y : Prop) : Prop := if op then x ∨ y else x ∧ y

theorem combineEval (op : Bool) (x y : Value (Binary.Tree B)) (ρ : B→Prop) :
    (combine op x y).truth (fun w => w.eval ρ) ↔
      logic op (x.truth (fun w => w.eval ρ)) (y.truth (fun w => w.eval ρ)) := by
  cases x with
  | bit a => cases a <;> cases y with
    | wire t => cases op <;> simp [combine,Value.truth,logic]
    | bit b => cases b <;> cases op <;> simp [combine,Value.truth,logic]
  | wire t => cases y with
    | wire u => cases op <;> rfl
    | bit b => cases b <;> cases op <;> simp [combine,Value.truth,logic]

/-- Translating a gate whose operands are already present adds at most one gate
to a shared prefix. Every old wire remains available. -/
theorem rebuildOne (op : Bool) (base : List (Binary.Tree B)) (ok : Built base)
    (x y : Value (Binary.Tree B)) (ax : available base x) (ay : available base y) :
    ∃ next : List (Binary.Tree B), Built next ∧ (∀ t,Ready base t → Ready next t) ∧
      available next (combine op x y) ∧ next.length ≤ base.length+1 := by
  cases x with
  | bit b =>
    cases b <;> cases op <;> exact ⟨base,ok,fun _ h => h,by simp_all [combine,available],by omega⟩
  | wire a =>
    cases y with
    | bit b =>
      cases b <;> cases op <;> exact ⟨base,ok,fun _ h => h,by simp_all [combine,available],by omega⟩
    | wire b =>
      refine ⟨(.gate op a b)::base,⟨ok,op,a,b,rfl,ax,ay⟩,?_,Or.inr (List.mem_cons_self ..),by simp⟩
      intro t h
      exact h.elim Or.inl (fun ht => Or.inr (List.mem_cons_of_mem _ ht))

def Signed (p : I→Prop) (n : J→Prop) (pos : I→B→Prop) (neg : J→B→Prop)
    (x : Value (Binary.Tree B)) : Prop :=
  (∀ i,p i → x.truth (fun w => w.eval (pos i))) ∧
    ∀ j,x.truth (fun w => w.eval (neg j)) → n j

theorem reuseSigned {p q : I→Prop} {n m : J→Prop} {pos : I→B→Prop} {neg : J→B→Prop}
    {x : Value (Binary.Tree B)} (old : Signed q m pos neg x)
    (hi : ∀ i,p i → q i) (lo : ∀ j,m j → n j) : Signed p n pos neg x :=
  ⟨fun i h => old.1 i (hi i h),fun j h => lo j (old.2 j h)⟩

theorem buildSigned {p q : I→Prop} {n m : J→Prop} {pos : I→B→Prop} {neg : J→B→Prop}
    {x y : Value (Binary.Tree B)} (sx : Signed p n pos neg x) (sy : Signed q m pos neg y)
    (op : Bool) : Signed (fun i => logic op (p i) (q i)) (fun j => logic op (n j) (m j))
      pos neg (combine op x y) := by
  constructor
  · intro i h
    apply (combineEval op x y (pos i)).mpr
    cases op
    · exact And.imp (sx.1 i) (sy.1 i) h
    · exact Or.imp (sx.1 i) (sy.1 i) h
  · intro j h
    have old := (combineEval op x y (neg j)).mp h
    cases op
    · exact And.imp (sx.2 j) (sy.2 j) old
    · exact Or.imp (sx.2 j) (sy.2 j) old

#print axioms combineEval
#print axioms rebuildOne
#print axioms reuseSigned
#print axioms buildSigned
end Checkpoint131.Rebuild
