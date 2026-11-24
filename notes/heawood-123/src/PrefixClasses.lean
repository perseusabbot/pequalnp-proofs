import PostedModel
import BottomPairs

namespace Checkpoint122.Prefix
open Finset Checkpoint122.Posted Checkpoint121.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls
open PEqualNP.Outside.L_meta_2268_aux.Normal

def first (i : Fin 65) : Stage.Port := (0,(Fin.ofNat 14 (key i/225)).val)
def second (i : Fin 65) : Stage.Port :=
  ((Fin.ofNat 15 (key i%225/15)).val,(Fin.ofNat 15 (key i%15)).val)

def firstSet (i : Fin 65) :=
  let xs := Stage.bases 14
  xs.getD (first i).1 ∅ ∪ xs.getD (first i).2 ∅
def secondSet (i : Fin 65) :=
  let xs := Stage.bases 14 ++ [firstSet i]
  xs.getD (second i).1 ∅ ∪ xs.getD (second i).2 ∅

def listed (i : Fin 65) := i.val ∈ [1,8,9,10,20]

def compatible (U W : Finset V) : Prop :=
  U ≠ W ∧ ∃ c d : V, ((c ∈ points ∧ d ∈ points) ∨ (c ∈ lines ∧ d ∈ lines)) ∧
    U ⊆ neighborhood c ∧ W ⊆ neighborhood d ∧
    (c≠d ∨ U=neighborhood c ∨ W=neighborhood d)

private theorem test : ∀ i : Fin 65, compatible (firstSet i) (secondSet i) ↔ listed i := by
  unfold compatible listed
  set_option maxRecDepth 16000 in
  set_option maxHeartbeats 5000000 in
  decide +kernel

private theorem libraryTest {B : List (Finset V)} (h : PairedBottom B) {U W}
    (hu : U ∈ B) (hw : W ∈ B) (ne : U≠W) : compatible U W := by
  classical
  obtain ⟨C,side,F,pairs,_,all⟩ := h
  have owns {S} (hs : S ∈ B) : ∃ c : C, S=neighborhood c ∨ S=F c := by
    have mem := List.mem_toFinset.mpr hs
    rw [all,mem_union] at mem
    rcases mem with t|t <;> obtain ⟨c,_,rfl⟩ := mem_image.mp t
    · exact ⟨c,Or.inl rfl⟩
    · exact ⟨c,Or.inr rfl⟩
  obtain ⟨c,hc⟩ := owns hu
  obtain ⟨d,hd⟩ := owns hw
  have sub {S} (v : C) (which : S=neighborhood v ∨ S=F v) : S ⊆ neighborhood v :=
    which.elim (fun eq => eq ▸ Subset.rfl) (fun eq => eq ▸ (pairs v).1)
  refine ⟨ne,c,d,?_,sub c hc,sub d hd,?_⟩
  · rcases side with h|h
    · exact Or.inl ⟨h ▸ c.property,h ▸ d.property⟩
    · exact Or.inr ⟨h ▸ c.property,h ▸ d.property⟩
  · by_cases distinct : c.val≠d.val
    · exact Or.inl distinct
    · have eq : c=d := Subtype.ext (not_ne_iff.mp distinct)
      subst d
      rcases hc with h|h
      · exact Or.inr (Or.inl h)
      rcases hd with k|k
      · exact Or.inr (Or.inr k)
      · exact False.elim (ne (h.trans k.symm))

/-- Any legal three-stage optimum beginning with the indicated two OR ports
uses one of the five listed representatives. -/
theorem physicalPrefix (i : Fin 65) (rest mid top : List Stage.Port) (out : ℕ)
    (legal : ∀ p ∈ mid, p.1 < 14+(first i::second i::rest).length ∧ p.2 < 14+(first i::second i::rest).length)
    (computes : ∀ z, PEqualNP.MetaComplexity.circuitFun 14 (Stage.circuit 14 (first i::second i::rest) mid top out) z = true ↔ predicate z)
    (size : (Stage.circuit 14 (first i::second i::rest) mid top out).size ≤ 27) : listed i := by
  let L := Stage.supportGates ((Stage.bases 14 ++ [firstSet i]) ++ [secondSet i]) rest
  have pairEq : Stage.sched 14 (first i::second i::rest) = (firstSet i::secondSet i::L).reverse := rfl
  have h := physicalBottom _ mid top out legal computes size
  have nd := h
  obtain ⟨_,_,_,_,distinct,_⟩ := nd
  rw [pairEq,List.nodup_reverse] at distinct
  apply (test _).mp
  apply libraryTest h
  · simp [pairEq]
  · simp [pairEq]
  · exact fun eq => (List.nodup_cons.mp distinct).1 (List.mem_cons.mpr (Or.inl eq))

def control (i : Fin 65) : List (Fin 8192) :=
  match i.val with
  | 1 => [4302, 4495, 4417, 4498, 4352, 4436, 4355, 4502, 4290, 4440, 4225, 4378, 1031, 1096, 1225, 1354, 1483, 1612, 1741, 5980, 6051, 6116, 6181, 6246, 6311]
  | 8 => [4302, 4224, 4497, 4417, 4499, 4352, 4437, 4355, 4503, 4431, 4225, 4378, 1031, 1160, 1289, 1418, 1547, 1612, 1741, 5980, 6051, 6116, 6181, 6246, 6311]
  | 9 => [4302, 4224, 4497, 4417, 4499, 4352, 4437, 4355, 4503, 4290, 4441, 4175, 1031, 1160, 1289, 1418, 1547, 1676, 1741, 5980, 6051, 6116, 6181, 6246, 6311]
  | 10 => [4302, 4224, 4497, 4417, 4499, 4352, 4437, 4355, 4503, 4303, 4225, 4378, 1031, 1160, 1289, 1418, 1547, 1612, 1741, 5980, 6051, 6116, 6181, 6246, 6311]
  | 20 => [4224, 4496, 4417, 4498, 4352, 4436, 4355, 4502, 4290, 4440, 4225, 4378, 967, 1096, 1225, 1354, 1483, 1612, 1741, 5980, 6051, 6116, 6181, 6246, 6311]
  | _ => []

/-- Five explicit schedules match the target on exactly the desk's packed inputs,
each using two initial OR gates and twenty-five more gates. -/
theorem certificates : ∀ i : Fin 65, listed i →
    (control i).length=25 ∧ output (codes i true true (control i))=2097151 := by
  unfold listed
  set_option maxRecDepth 16000 in
  set_option maxHeartbeats 5000000 in
  decide +kernel

#print axioms physicalPrefix
#print axioms certificates
end Checkpoint122.Prefix
