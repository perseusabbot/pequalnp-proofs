import PostedModel
import ResidualShapes
import Restoration

namespace Checkpoint124.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Shapes
open PEqualNP.Outside.L_meta_3004_aux.Controls

theorem smallRestoration (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (mark : none∈((run 14 gs).wires.getD out default).tags) (small : price gs out ≤ 4) :
    missed ((run 14 gs).wires.getD out default) ≤ cap (price gs out) := by
  obtain ⟨q,hq,cut,f,hf,lim⟩ := residualTerms gs out spec mark
  exact lim.trans (lengthBound small hq cut hf)

/-- In a correct circuit of at most 26 gates, at least six distinct positive
edge inputs disappear under pruning, and at least five exceptional gates occur. -/
theorem sixLost (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length ≤ 26) :
    let w := (run 14 gs).wires.getD out default
    6 ≤ missed w ∧ 5 ≤ price gs out ∧ 4*(survivors w).card ≤ 3*(gs.length-5) := by
  let s := run 14 gs
  let w := s.wires.getD out default
  let k := price gs out
  obtain ⟨mark,_,three,_,_⟩ := nestedNecessary gs out spec short
  change 3 ≤ missed w at three
  have cost := priceBudget gs out spec mark
  change (survivors w).card+w.jobs.card+k ≤ gs.length at cost
  have bud := budget (run_valid 14 gs).1 out spec
  have stars := bud.cubic
  change (survivors w).card ≤ 3*w.jobs.card at stars
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have total : missed w+(survivors w).card=21 := by
    have sub : survivors w⊆G.edgeFinset := bud.sub
    have bound := card_le_card sub
    rw [missed,card_sdiff_of_subset sub,tally]
    rw [tally] at bound
    omega
  have limited (small : k ≤ 4) : missed w ≤ cap k := smallRestoration gs out spec mark small
  have six : 6 ≤ missed w := by
    by_contra! fewer
    have small : k ≤ 4 := by omega
    have term := limited small
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 by omega) with h|h|h|h|h <;> rw [h] at term <;>
      simp only [cap] at term <;> omega
  have five : 5 ≤ k := by
    by_contra! small
    have term := limited (by omega)
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 by omega) with h|h|h|h|h <;> rw [h] at term <;>
      simp only [cap] at term <;> omega
  refine ⟨six,five,?_⟩
  change 4*(survivors w).card ≤ 3*(gs.length-5)
  omega

/-- At six missing edges there must be at least 25 gates and five or six
surviving products. At 25 gates the count of surviving products is exactly five. -/
theorem sixProfile (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length ≤ 26) (lost : missed ((run 14 gs).wires.getD out default)=6) :
    let w := (run 14 gs).wires.getD out default
    25 ≤ gs.length ∧ 5 ≤ w.jobs.card ∧ w.jobs.card ≤ 6 ∧
      (gs.length=25 → w.jobs.card=5 ∧ price gs out=5) := by
  let w := (run 14 gs).wires.getD out default
  have bud := budget (run_valid 14 gs).1 out spec
  have sub : survivors w⊆G.edgeFinset := bud.sub
  have stars := bud.cubic
  change (survivors w).card ≤ 3*w.jobs.card at stars
  have tally : G.edgeFinset.card=21 := by decide +kernel
  change missed w=6 at lost
  rw [missed,card_sdiff_of_subset sub,tally] at lost
  have cost := priceBudget gs out spec (nestedNecessary gs out spec short).1
  change (survivors w).card+w.jobs.card+price gs out ≤ gs.length at cost
  have five := (sixLost gs out spec short).2.1
  change 25 ≤ gs.length ∧ 5 ≤ w.jobs.card ∧ w.jobs.card ≤ 6 ∧
    (gs.length=25 → w.jobs.card=5 ∧ price gs out=5)
  omega

theorem smallerCircuits (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length ≤ 24) :
    let w := (run 14 gs).wires.getD out default
    7 ≤ missed w ∧ (gs.length ≤ 23 → 8 ≤ missed w) ∧ (gs.length ≤ 22 → 9 ≤ missed w) := by
  let w := (run 14 gs).wires.getD out default
  have sub : survivors w⊆G.edgeFinset := (budget (run_valid 14 gs).1 out spec).sub
  have bound := (sixLost gs out spec (by omega)).2.2
  change 4*(survivors w).card ≤ 3*(gs.length-5) at bound
  have tally : G.edgeFinset.card=21 := by decide +kernel
  change 7 ≤ missed w ∧ (gs.length ≤ 23 → 8 ≤ missed w) ∧ (gs.length ≤ 22 → 9 ≤ missed w)
  rw [missed,card_sdiff_of_subset sub,tally]
  omega

/-- The desk's packed evaluator, with any of its 65 openings and either
operation on each opening wire pair, obeys the same loss bound. -/
theorem postedSixLost (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (h : Checkpoint122.Posted.Witness i f g tail) :
    let qs := Checkpoint122.Posted.codes i f g tail
    6 ≤ missed ((run 14 (qs.map Checkpoint122.Posted.decode)).wires.getD (13+qs.length) default) := by
  apply (sixLost _ _ (Checkpoint122.Posted.semantics _ h.2) ?_).1
  have len := h.1
  simp only [List.length_map,Checkpoint122.Posted.codes,List.length_cons]
  omega

#print axioms smallRestoration
#print axioms sixLost
#print axioms sixProfile
#print axioms smallerCircuits
#print axioms postedSixLost
end Checkpoint124.Heawood
