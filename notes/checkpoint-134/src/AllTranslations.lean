import Minimum
import CyclicAction

namespace Checkpoint134
open Finset
open PEqualNP.Outside.L_meta_9338 (V Box legal)

/-- The full cyclic translation orbit of any cover using at most fourteen rectangles. -/
theorem smallCoverTranslations {s : Finset Box} (g : ∀b∈s,legal b) (complete : covers s)
    (small : s.card≤14) : (univ.image (fun k : V => translated k s)).card=21 :=
  orbitOfLower stableMinimum g complete (by omega)

theorem forwardListMinimum (L : List Box) (g : ∀b∈L,legal b) (complete : covers L.toFinset)
    (closed : ∀b∈L,addSeven b∈L) : 15≤L.length :=
  listMinimum L g complete ((stableForward _).mpr fun b h =>
    List.mem_toFinset.mpr (closed b (List.mem_toFinset.mp h)))

/-- A finite translation-closed collection of covers of size at most fourteen splits into blocks of 21. -/
theorem coverCountDivisible (u : Finset (Finset Box))
    (good : ∀s∈u,(∀b∈s,legal b) ∧ covers s ∧ s.card≤14)
    (closed : ∀s∈u,∀k : V,translated k s∈u) : 21 ∣ u.card := by
  apply countByOrbits u _ closed
  intro s hs
  obtain ⟨g,c,small⟩ := good s hs
  exact smallCoverTranslations g c small

#print axioms forwardListMinimum
#print axioms coverCountDivisible
#print axioms smallCoverTranslations
end Checkpoint134
