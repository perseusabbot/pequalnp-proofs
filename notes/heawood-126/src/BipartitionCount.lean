import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2268_aux.Price

theorem smallCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (col : G.Colorable 2)
    (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      (∀ u ∈ T, ∀ v ∈ T, ¬G.Adj u v) ∧
      G.edgeFinset.card + T.card ≤ 2 * (n - A.card) := by
  classical
  obtain ⟨color⟩ := col
  let B : Finset (Fin n) := Aᶜ
  have memB (v : Fin n) : v ∈ B ↔ v ∉ A := Finset.mem_compl
  have cardB : B.card = n - A.card := by simp [B, Finset.card_compl]
  have restrict : ∑ v ∈ B, G.degree v = ∑ v, G.degree v := by
    apply Finset.sum_subset (Finset.subset_univ B)
    intro v _ h
    apply (G.degree_eq_zero v).mpr
    exact fun w e => h ((memB v).mpr (iso v w e))
  have count : 2 * G.edgeFinset.card = 3 * B.card := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ = ∑ v ∈ B, G.degree v := restrict.symm
      _ = ∑ _v ∈ B, 3 := by
        apply Finset.sum_congr rfl
        intro v h
        simpa only [G.ncard_neighborSet] using reg v ((memB v).mp h)
      _ = 3 * B.card := by simp [Nat.mul_comm]
  let p : Fin n → Prop := fun v => color v = 0
  let L := B.filter p
  let R := B.filter (fun v => ¬ p v)
  have left (v : Fin n) : v ∈ L ↔ v ∈ B ∧ p v := Finset.mem_filter
  have right (v : Fin n) : v ∈ R ↔ v ∈ B ∧ ¬ p v := Finset.mem_filter
  have sizes : L.card + R.card = B.card := Finset.card_filter_add_card_filter_not p
  have colors : ∀ i j : Fin 2, i ≠ j → (i = 0 ↔ j ≠ 0) := by decide
  have opposite {u v : Fin n} (e : G.Adj u v) : p u ↔ ¬p v :=
    colors (color u) (color v) (color.valid e)
  have ends {u v : Fin n} (e : G.Adj u v) : u ∈ B ∧ v ∈ B :=
    ⟨(memB u).mpr (iso u v e), (memB v).mpr (iso v u e.symm)⟩
  by_cases small : L.card ≤ R.card
  · refine ⟨L, ?_, ?_, by omega⟩
    · intro u v e
      by_cases hu : p u
      · exact Or.inl ((left u).mpr ⟨(ends e).1, hu⟩)
      · exact Or.inr ((left v).mpr ⟨(ends e).2, (opposite e.symm).mpr hu⟩)
    · intro u hu v hv e
      exact (opposite e).mp ((left u).mp hu).2 ((left v).mp hv).2
  · refine ⟨R, ?_, ?_, by omega⟩
    · intro u v e
      by_cases hu : p u
      · exact Or.inr ((right v).mpr ⟨(ends e).2, (opposite e).mp hu⟩)
      · exact Or.inl ((right u).mpr ⟨(ends e).1, hu⟩)
    · intro u hu v hv e
      exact ((right u).mp hu).2 ((opposite e).mpr ((right v).mp hv).2)

end PEqualNP.Outside.L_meta_2268_aux.Price
