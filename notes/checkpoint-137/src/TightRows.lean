import MaximumRectangles
import Overlaps

namespace Checkpoint137

open Finset PEqualNP.Outside.L_meta_9338

set_option maxHeartbeats 0 in
private theorem ovalSizes : ∀ h : H, (oval h).1.card = 6 ∧ (oval h).2.card = 6 := by
  decide +kernel

/-- A triple covering all sixteen zeros at a row also covers sixteen zeros at a common column. -/
theorem pairedPencils (a b c : H) (p : V)
    (pa : p ∈ (oval a).1) (pb : p ∈ (oval b).1) (pc : p ∈ (oval c).1)
    (full : ((oval a).2 ∪ (oval b).2 ∪ (oval c).2).card = 16) :
    (∃! q : V, q ∈ (oval a).2 ∧ q ∈ (oval b).2 ∧ q ∈ (oval c).2) ∧
    ((oval a).1 ∪ (oval b).1 ∪ (oval c).1).card = 16 := by
  have meet {i j : H} (hi : p ∈ (oval i).1) (hj : p ∈ (oval j).1) :
      0 < ((oval i).2 ∩ (oval j).2).card := by
    rw [← (balancedPairs i j : ((oval i).1 ∩ (oval j).1).card = _)]
    exact card_pos.mpr ⟨p,mem_inter.mpr ⟨hi,hj⟩⟩
  obtain ⟨ab,ac,bc,abc⟩ := tightTriple (ovalSizes a).2 (ovalSizes b).2 (ovalSizes c).2
    (meet pa pb) (meet pa pc) (meet pb pc) full
  constructor
  · obtain ⟨q,eq⟩ := card_eq_one.mp abc
    have iff (x : V) : (x ∈ (oval a).2 ∧ x ∈ (oval b).2 ∧ x ∈ (oval c).2) ↔ x = q := by
      have idem : x ∈ (oval a).2 ∩ (oval b).2 ∩ (oval c).2 ↔ x = q := by rw [eq,mem_singleton]
      simpa [and_assoc] using idem
    exact ⟨q,(iff q).mpr rfl,fun x hx => (iff x).mp hx⟩
  · have xy : ((oval a).1 ∩ (oval b).1).card = 1 := (balancedPairs a b).trans ab
    have xz : ((oval a).1 ∩ (oval c).1).card = 1 := (balancedPairs a c).trans ac
    have yz : ((oval b).1 ∩ (oval c).1).card = 1 := (balancedPairs b c).trans bc
    have lower : 0 < ((oval a).1 ∩ (oval b).1 ∩ (oval c).1).card :=
      card_pos.mpr ⟨p,mem_inter.mpr ⟨mem_inter.mpr ⟨pa,pb⟩,pc⟩⟩
    have upper := card_le_card (inter_subset_left (s₁ := (oval a).1 ∩ (oval b).1) (s₂ := (oval c).1))
    have tally := cardJoin (oval a).1 (oval b).1 (oval c).1
    rw [xy,xz,yz,(ovalSizes a).1,(ovalSizes b).1,(ovalSizes c).1] at tally
    omega

#print axioms pairedPencils

end Checkpoint137
