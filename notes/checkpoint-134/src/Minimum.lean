import CoverCertificates
import Four1Checks
import Four4Checks
import Four6Checks
import Four13Checks
import Move2Checks
import Move3Checks
import Fixed2Checks
import Fixed3Checks

namespace Checkpoint134
open PEqualNP.Outside.L_meta_9338 (Box legal)
theorem noFour (k : Actions.Class) (a : Fin 4→Box) (g : ∀t,legal (a t)) (c : PairSlots k a) : False :=
  noFourFrom Four1.finiteChecks Four4.finiteChecks Four6.finiteChecks Four13.finiteChecks k a g c

theorem noTwo (a : Fin 2→Box) (d : Fin 14→FixedPool.Index) (g : ∀t,legal (a t)) (c : Slots 2 14 a d) : False :=
  noTwoFrom Move2.finiteChecks Fixed2.finiteChecks a d g c

theorem noThree (a : Fin 3→Box) (d : Fin 5→FixedPool.Index) (g : ∀t,legal (a t)) (c : Slots 3 5 a d) : False :=
  noThreeFrom Move3.finiteChecks Fixed3.finiteChecks a d g c

theorem stableMinimum {s : Finset Box} (g : ∀b∈s,legal b) (complete : covers s) (closed : stable s) :
    15≤s.card := familyLower noTwo noThree noFour g complete closed

theorem listMinimum (L : List Box) (g : ∀b∈L,legal b) (complete : covers L.toFinset)
    (closed : stable L.toFinset) : 15≤L.length :=
  (stableMinimum (fun b hb => g b (List.mem_toFinset.mp hb)) complete closed).trans (List.toFinset_card_le L)

theorem exactMinimum : (∃ L : List Box,L.length=15 ∧ (∀b∈L,legal b) ∧ covers L.toFinset ∧ stable L.toFinset) ∧
    ∀ L : List Box,(∀b∈L,legal b) → covers L.toFinset → stable L.toFinset → 15≤L.length :=
  ⟨incumbent,listMinimum⟩

#print axioms noFour
#print axioms noThree
#print axioms noTwo
#print axioms stableMinimum
#print axioms exactMinimum
end Checkpoint134
