import Sharp
import R_meta_2084_121
import L_meta_2084_child1
import Literals

namespace Checkpoint121.Cubic
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- The remaining cost-preserving conversion is equivalent to the exact posted lower bound. -/
theorem parentIffNormalization :
  (∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ)) ↔
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 : Fin x12 → Finset (Fin x1)) (x14 : Fin x12 → Finset (Fin x1)), (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 : Finset (Fin x1)) (x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ (1 : ℕ) ∨ x19 ∈ x17) ∧ (x20.card ≤ (1 : ℕ) ∨ x20 ∈ x17)) ∧ (∀ (x15 : Fin x12), ((x13 x15).card ≤ (1 : ℕ) ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ (1 : ℕ) ∨ x14 x15 ∈ x11)) ∧ (∀ (x15 : Fin x1 → Bool), (∃ (x16 : Fin x12), (∃ x17 ∈ x13 x16, x15 x17 = Bool.true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = Bool.true) ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ x11.length + (2 : ℕ) * x12 ≤ x9 + (1 : ℕ)) := by
  constructor
  · intro parent n G _ A cubic girth iso edge s pure
    classical
    let eligible (k : ℕ) := ∃ V : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ V ∨ v ∈ V) ∧ V.card = k
    have anyCover : ∃ k, eligible k :=
      ⟨(Finset.univ : Finset (Fin n)).card,Finset.univ,by simp,rfl⟩
    let k := Nat.find anyCover
    obtain ⟨V,cover,card⟩ := Nat.find_spec anyCover
    have demand : ∀ W : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ W ∨ v ∈ W) → k ≤ W.card :=
      fun W h => Nat.find_min' anyCover ⟨W,h,rfl⟩
    have joined := PEqualNP.Outside.L_meta_2268_aux.Literals.appendSet A (graphFun G ∅) pure
    have same : (fun x => decide (∃ v ∈ A, x v = true) || graphFun G ∅ x) = graphFun G A := by
      funext x
      simp [graphFun]
    rw [same] at joined
    have bound := parent n k G A (graphFun G A) cubic girth iso edge demand
      (fun x => by simp [graphFun]) _ joined
    obtain ⟨B,m,X,Y,build,ready,truth,cost⟩ := coverRepresentation G V cover
    refine ⟨B,m,X,Y,build,ready,truth,?_⟩
    change V.card = k at card
    omega
  · exact PEqualNP.Outside.R_meta_2084_121 PEqualNP.Outside.L_meta_2084_child1 PEqualNP.Outside.L_meta_2084_child2

#print axioms parentIffNormalization
end Checkpoint121.Cubic
