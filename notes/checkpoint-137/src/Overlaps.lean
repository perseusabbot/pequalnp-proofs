import PEqualNP.Outside.L_meta_9338

namespace Checkpoint137

open Finset PEqualNP.Outside.L_meta_9338

def balanced (h k : H) :=
  ((oval h).1 ∩ (oval k).1).card = ((oval h).2 ∩ (oval k).2).card

set_option maxHeartbeats 0 in
private theorem overlapAtZero : ∀ k : H, balanced 0 k := by
  unfold balanced
  decide +kernel

private theorem movedCard (f : V → V) (hf : Function.Injective f) (A B : Finset V) :
    (A.image f ∩ B.image f).card = (A ∩ B).card := by
  rw [← image_inter A B hf, card_image_of_injective _ hf]

private theorem actBalanced (g : G) (h k : H) : balanced (act g h) (act g k) ↔ balanced h k := by
  have hr : Function.Injective (permR g) := Finite.injective_iff_surjective.mpr (genFacts g).2.1
  have hc : Function.Injective (permC g) := Finite.injective_iff_surjective.mpr (genFacts g).2.2
  unfold balanced
  rw [← genOval g h, ← genOval g k]
  simp only [moved, movedCard _ hr, movedCard _ hc]

private theorem walkBalanced (w : List G) (h k : H) :
    balanced (walk w h) (walk w k) ↔ balanced h k := by
  induction w generalizing h k with
  | nil => rfl
  | cons g ws ih => exact (ih (act g h) (act g k)).trans (actBalanced g h k)

theorem balancedPairs (h k : H) : balanced h k := by
  let w := firstMoves[h.val]!
  apply (walkBalanced w h k).mp
  rw [show walk w h = 0 from startFacts.1 h]
  exact overlapAtZero _

#print axioms balancedPairs

end Checkpoint137
