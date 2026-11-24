import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2268_aux.Normal

open Finset

/-- Cubic degree count on the complement of the isolated, marked vertices. -/
theorem cubicDegreeSum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A) :
    2 * G.edgeFinset.card = 3 * (n - A.card) := by
  classical
  have restrict : ∑ v ∈ Aᶜ, G.degree v = ∑ v, G.degree v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ h
    apply (G.degree_eq_zero v).mpr
    exact fun w e => h (Finset.mem_compl.mpr (iso v w e))
  calc
    2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
    _ = ∑ v ∈ Aᶜ, G.degree v := restrict.symm
    _ = ∑ _v ∈ Aᶜ, 3 := by
      apply Finset.sum_congr rfl
      intro v h
      simpa only [G.ncard_neighborSet] using reg v (Finset.mem_compl.mp h)
    _ = 3 * (n - A.card) := by simp [Finset.card_compl, Nat.mul_comm]

/-- Each term covers at most its number of leaves and has at most three leaves. -/
theorem starCounts {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A)
    (center : Fin m → Fin n) (leaves : Fin m → Finset (Fin n))
    (clean : ∀ i v, v ∈ leaves i → G.Adj (center i) v)
    (cover : ∀ e ∈ G.edgeFinset, ∃ i v, v ∈ leaves i ∧ e = s(center i, v)) :
    G.edgeFinset.card ≤ ∑ i, (leaves i).card ∧ (∑ i, (leaves i).card) ≤ 3*m := by
  classical
  let parts (i : Fin m) : Finset (Sym2 (Fin n)) := (leaves i).image (fun v => s(center i, v))
  have inc : G.edgeFinset ⊆ Finset.univ.biUnion parts := by
    intro e he
    obtain ⟨i,v,hv,rfl⟩ := cover e he
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image_of_mem _ hv⟩
  constructor
  · calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion parts).card := card_le_card inc
      _ ≤ ∑ i, (parts i).card := card_biUnion_le
      _ ≤ ∑ i, (leaves i).card := sum_le_sum fun _ _ => card_image_le
  · have leafBound (i : Fin m) : (leaves i).card ≤ 3 := by
      by_cases h : (leaves i).Nonempty
      · obtain ⟨v,hv⟩ := h
        have incl : leaves i ⊆ G.neighborFinset (center i) := fun w hw =>
          (G.mem_neighborFinset _ _).mpr (clean i w hw)
        have hc := card_le_card incl
        have deg := reg (center i) (iso _ _ (clean i v hv))
        simpa only [G.card_neighborFinset_eq_degree, ← G.ncard_neighborSet, deg] using hc
      · simp [Finset.not_nonempty_iff_eq_empty.mp h]
    calc
      (∑ i, (leaves i).card) ≤ ∑ _i : Fin m, 3 := sum_le_sum fun i _ => leafBound i
      _ = 3*m := by simp [Nat.mul_comm]

/-- With independent ORs for each star's leaves, one AND per star, and a final
OR of the terms, the gate count is the number of leaves plus terms, minus one. -/
theorem starFormulaLower {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A)
    (center : Fin m → Fin n) (leaves : Fin m → Finset (Fin n))
    (clean : ∀ i v, v ∈ leaves i → G.Adj (center i) v)
    (cover : ∀ e ∈ G.edgeFinset, ∃ i v, v ∈ leaves i ∧ e = s(center i, v)) :
    2 * (n - A.card) - 1 ≤ (∑ i, (leaves i).card) + m - 1 := by
  obtain ⟨hc, hm⟩ := starCounts G A reg iso center leaves clean cover
  have hs := cubicDegreeSum G A reg iso
  omega

end PEqualNP.Outside.L_meta_2268_aux.Normal
