import PhysicalStages
import L_meta_2084_child2

namespace Checkpoint121.Cubic
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2268_aux.Normal
open PEqualNP.Outside.L_meta_2268_aux.Normal.Stage
open StarUnion

/-- Turn the recursive union schedule into the split-at-any-gate condition used on the desk. -/
theorem scheduledAt {n} (P : List (Finset (Fin n))) (a : Finset (Fin n))
    (T : List (Finset (Fin n))) (h : Built (P ++ a :: T)) :
    ∃ b c, a = b ∪ c ∧ Ready T b ∧ Ready T c := by
  induction P with
  | nil => exact h.2
  | cons head P ih => exact ih h.1

/-- Extract exactly the usable middle gates from the designated physical output.
The three circuit stages may contain redundant gates and shared wires. -/
theorem stages {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bot mid top : List Port) (out : ℕ)
    (valid : ∀ p ∈ mid, p.1 < n+bot.length ∧ p.2 < n+bot.length)
    (computes : ∀ z, circuitFun n (circuit n bot mid top out) z = true ↔
      ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) :
    ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ (P : List (Finset (Fin n))) a T, B = P ++ a :: T →
        ∃ b c, a = b ∪ c ∧ Ready T b ∧ Ready T c) ∧
      (∀ i, Ready B (X i) ∧ Ready B (Y i)) ∧
      (∀ z, coverTruth X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) ∧
      B.length + 2*m ≤ (circuit n bot mid top out).size + 1 := by
  classical
  let S := (sourceWires mid.length top).getD out ∅
  let src (i : Fin S.card) : Fin mid.length := (S.equivFin.symm i).val
  let X (i : Fin mid.length) := (sourceWires n bot).getD (mid[i].1) ∅
  let Y (i : Fin mid.length) := (sourceWires n bot).getD (mid[i].2) ∅
  refine ⟨sched n bot,S.card,X ∘ src,Y ∘ src,?_,?_,?_,?_⟩
  · intro P a T eqn
    exact scheduledAt P a T (eqn ▸ (scheduled n bot).1)
  · intro i
    exact ⟨(scheduled n bot).2 _,(scheduled n bot).2 _⟩
  · intro z
    have reach : reachableTruth S X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true :=
      (physicalTruth n bot mid top out valid z).symm.trans (computes z)
    apply Iff.trans _ reach
    constructor
    · rintro ⟨i,hu,hv⟩
      exact ⟨src i,(S.equivFin.symm i).property,hu,hv⟩
    · rintro ⟨i,hi,hu,hv⟩
      let j : S := ⟨i,hi⟩
      exact ⟨S.equivFin j,by simpa [Function.comp_def,src,j] using hu,
        by simpa [Function.comp_def,src,j] using hv⟩
  · have lower : S.card ≤ (sched mid.length top).length+1 :=
      collectorBound _ (scheduled mid.length top).1 _ ((scheduled mid.length top).2 out)
    have upper : S.card ≤ mid.length := by simpa using card_le_univ S
    simp only [sched,List.length_reverse,supportLength] at lower ⊢
    rw [physicalSize]
    omega

/-- The edge count and one vertex-cover cost give a lower bound on every
physical three-stage implementation, without regularity or bipartiteness. -/
theorem physicalCoverBound {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (bot mid top : List Port) (out : ℕ)
    (valid : ∀ p ∈ mid, p.1 < n+bot.length ∧ p.2 < n+bot.length)
    (computes : ∀ z, circuitFun n (circuit n bot mid top out) z = true ↔
      ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) :
    ∃ V : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ V ∨ v ∈ V) ∧
      G.edgeSet.ncard + V.card ≤ (circuit n bot mid top out).size + 1 := by
  obtain ⟨B,m,X,Y,build,ready,truth,sz⟩ := stages G bot mid top out valid computes
  obtain ⟨V,cover,bound⟩ := PEqualNP.Outside.L_meta_2084_child2 n G girth B m X Y build ready truth
  exact ⟨V,cover,bound.trans sz⟩

#print axioms stages
#print axioms physicalCoverBound
end Checkpoint121.Cubic
