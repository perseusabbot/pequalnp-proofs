import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.Perm.Basic
import PEqualNP.Outside.L_meta_9338

namespace Checkpoint136
open PEqualNP.Outside.L_meta_9338 (V bit)
open MulAction

/-- All independent permutations of the two axes preserving the posted incidence matrix. -/
def boardGroup : Subgroup (Equiv.Perm V × Equiv.Perm V) where
  carrier := {g | ∀i j, bit (g.1 i) (g.2 j) = bit i j}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb i j
    exact (ha (b.1 i) (b.2 j)).trans (hb i j)
  inv_mem' := by
    intro a ha i j
    simpa using (ha (a.1.symm i) (a.2.symm j)).symm

abbrev Axis := ↥boardGroup
abbrev row (g : Axis) := g.val.1
abbrev col (g : Axis) := g.val.2

instance boardAction : MulAction Axis V := MulAction.compHom V
  ((MonoidHom.fst (Equiv.Perm V) (Equiv.Perm V)).comp boardGroup.subtype)

def fixing (s : List V) : Subgroup Axis where
  carrier := {g | ∀ x∈s, row g x=x}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro f g hf hg x hx
    change row f (row g x)=x
    rw [hg x hx,hf x hx]
  inv_mem' := by
    intro f hf x hx
    exact (row f).symm_apply_eq.mpr (hf x hx).symm

private def nextLevel (s : List V) (a : V) :
    stabilizer (fixing s) a ≃ fixing (a::s) where
  toFun f := ⟨f.val.val,by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact f.property
    · exact f.val.property x hx⟩
  invFun f := ⟨⟨f.val,fun x hx => f.property x (List.mem_cons_of_mem _ hx)⟩,
    f.property a List.mem_cons_self⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stepCard (s : List V) (a : V) (choices : Finset V)
    (upper : ∀g : fixing s, row g.val a ∈ choices)
    (lower : ∀v∈choices, ∃g : fixing s, row g.val a=v) :
    Nat.card (fixing s) = choices.card * Nat.card (fixing (a::s)) := by
  have eq : orbit (fixing s) a = (↑choices : Set V) := by
    ext v
    constructor
    · rintro ⟨g,rfl⟩
      exact upper g
    · exact lower v
  have fact := Nat.card_congr (orbitProdStabilizerEquivGroup (fixing s) a)
  rw [Nat.card_prod,eq,Nat.card_congr (nextLevel s a)] at fact
  simpa using fact.symm

theorem fixedLine (g : Axis) {a b l : V}
    (ha : row g a=a) (hb : row g b=b)
    (pa : bit a l=true) (pb : bit b l=true)
    (alone : ∀z, bit a z=true → bit b z=true → z=l) : col g l=l := by
  apply alone
  · simpa [ha] using (g.property a l).trans pa
  · simpa [hb] using (g.property b l).trans pb

theorem fixedPoint (g : Axis) {l m a : V}
    (hl : col g l=l) (hm : col g m=m)
    (pl : bit a l=true) (pm : bit a m=true)
    (alone : ∀z, bit z l=true → bit z m=true → z=a) : row g a=a := by
  apply alone
  · simpa [hl] using (g.property a l).trans pl
  · simpa [hm] using (g.property a m).trans pm

def compatible (points lines : List V) (a b : V) : Prop :=
  (∀p∈points, (a=p ↔ b=p)) ∧ (∀l∈lines, bit a l=bit b l)

theorem imageCompatible (g : Axis) {points lines : List V} (a : V)
    (hp : ∀p∈points,row g p=p) (hl : ∀l∈lines,col g l=l) :
    compatible points lines a (row g a) := by
  constructor
  · intro p h
    constructor
    · rintro rfl
      exact hp _ h
    · intro e
      exact (row g).injective (e.trans (hp p h).symm)
  · intro l h
    simpa [hl l h] using (g.property a l).symm

theorem extendMembership {K : Subgroup Axis} {s : List V} {a : V}
    (step : ∀g : fixing s, ∃h : fixing s, h.val∈K ∧ row h.val a=row g.val a)
    (rest : ∀g : fixing (a::s),g.val∈K) : ∀g : fixing s,g.val∈K := by
  intro g
  obtain ⟨h,member,hit⟩ := step g
  let d : fixing (a::s) := ⟨h.val⁻¹*g.val,by
    intro x hx
    change (row h.val).symm (row g.val x)=x
    apply (row h.val).symm_apply_eq.mpr
    rcases List.mem_cons.mp hx with rfl|inTail
    · exact hit.symm
    · rw [g.property x inTail,h.property x inTail]⟩
  have done := K.mul_mem member (rest d)
  change h.val*(h.val⁻¹*g.val)∈K at done
  simpa using done

private def emptyLevel : fixing [] ≃ Axis where
  toFun := Subtype.val
  invFun g := ⟨g,by simp [fixing]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem emptyCard : Nat.card Axis=Nat.card (fixing []) := (Nat.card_congr emptyLevel).symm

end Checkpoint136
