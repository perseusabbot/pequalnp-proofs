import ForcedInputs

namespace Checkpoint130.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def edgeOn (z : V→Bool) : Bool := edges.any fun e => z (Fin.ofNat 14 e.1) && z (Fin.ofNat 14 e.2)

theorem edgeOnCorrect (z : V→Bool) : edgeOn z=true ↔ predicate z := by
  have bounds : ∀ e∈edges,e.1<14 ∧ e.2<14 := by decide +kernel
  constructor
  · intro h
    obtain ⟨⟨u,v⟩,mem,bits⟩ := List.any_eq_true.mp h
    obtain ⟨hu,hv⟩ := bounds _ mem
    obtain ⟨on,other⟩ := Bool.and_eq_true_iff.mp bits
    exact ⟨Fin.ofNat 14 u,Fin.ofNat 14 v,by simpa [Fin.ofNat,Nat.mod_eq_of_lt hu,Nat.mod_eq_of_lt hv] using mem,on,other⟩
  · rintro ⟨u,v,h,hu,hv⟩
    apply List.any_eq_true.mpr
    exact ⟨_,h,by simpa [Fin.ofNat,Nat.mod_eq_of_lt u.isLt,Nat.mod_eq_of_lt v.isLt] using Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩

def rowDec (z : V→Bool) : Decidable (predicate z) := decidable_of_iff (edgeOn z=true) (edgeOnCorrect z)

#print axioms edgeOnCorrect
end Checkpoint130.Heawood
