import Mathlib.Combinatorics.SimpleGraph.Paths
import StarFormula

namespace PEqualNP.Outside.L_meta_2268_aux.Normal

open Finset SimpleGraph

theorem noSquare {n : ℕ} (G : SimpleGraph (Fin n))
    (girth : ∀ z (p : G.Walk z z), p.IsCycle → 5 ≤ p.length)
    {i j k l : Fin n} (ij : G.Adj i j) (jk : G.Adj j k)
    (kl : G.Adj k l) (li : G.Adj l i) (ik : i ≠ k) (jl : j ≠ l) : False := by
  let p : G.Walk i i := .cons ij (.cons jk (.cons kl (.cons li .nil)))
  have cyc : p.IsCycle := by
    refine Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [p]⟩
    simp [p, Walk.tail_cons, ij.ne.symm, jk.ne, kl.ne, li.ne, ik.symm, jl]
  have too := girth i p cyc
  change 5 ≤ 4 at too
  omega

/-- A clean product has at most three cross pairs and uses at least four input
occurrences per three pairs. Empty sides are allowed. -/
theorem cleanProductCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A)
    (girth : ∀ z (p : G.Walk z z), p.IsCycle → 5 ≤ p.length)
    (X Y : Finset (Fin n)) (clean : ∀ u ∈ X, ∀ v ∈ Y, G.Adj u v) :
    X.card * Y.card ≤ 3 ∧ 4 * (X.card * Y.card) ≤ 3 * (X.card + Y.card) := by
  classical
  by_cases hx : X.Nonempty
  · by_cases hy : Y.Nonempty
    · obtain ⟨x,hx⟩ := hx
      obtain ⟨y,hy⟩ := hy
      have bound (v : Fin n) (S : Finset (Fin n)) (hv : v ∉ A)
          (adj : ∀ w ∈ S, G.Adj v w) : S.card ≤ 3 := by
        have inc : S ⊆ G.neighborFinset v := fun w hw => (G.mem_neighborFinset _ _).mpr (adj w hw)
        have hc := card_le_card inc
        simpa only [G.card_neighborFinset_eq_degree, ← G.ncard_neighborSet, reg v hv] using hc
      have xBound := bound y X (iso _ _ (clean x hx y hy).symm) fun w hw => (clean w hw y hy).symm
      have yBound := bound x Y (iso _ _ (clean x hx y hy)) (clean x hx)
      have sides : X.card = 1 ∨ Y.card = 1 := by
        by_contra! h
        have xpos : 0 < X.card := Finset.card_pos.mpr ⟨x,hx⟩
        have ypos : 0 < Y.card := Finset.card_pos.mpr ⟨y,hy⟩
        obtain ⟨u,hu,w,hw,uw⟩ := Finset.one_lt_card.mp (show 1 < X.card by omega)
        obtain ⟨v,hv,z,hz,vz⟩ := Finset.one_lt_card.mp (show 1 < Y.card by omega)
        exact noSquare G girth (clean u hu v hv) (clean w hw v hv).symm
          (clean w hw z hz) (clean u hu z hz).symm uw vz
      rcases sides with sx | sy
      · rw [sx, one_mul]
        omega
      · rw [sy, mul_one]
        omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hy]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hx]

/-- The OR of clean products of two ORs cannot beat the star-cover benchmark
when each input occurrence in the displayed formula is charged separately. -/
theorem bicliqueFormulaLower {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A)
    (girth : ∀ z (p : G.Walk z z), p.IsCycle → 5 ≤ p.length)
    (X Y : Fin m → Finset (Fin n))
    (clean : ∀ i u, u ∈ X i → ∀ v, v ∈ Y i → G.Adj u v)
    (cover : ∀ e ∈ G.edgeFinset, ∃ i u v, u ∈ X i ∧ v ∈ Y i ∧ e = s(u,v)) :
    2 * (n - A.card) - 1 ≤ (∑ i, ((X i).card + (Y i).card)) - 1 := by
  classical
  let rect (i : Fin m) : Finset (Sym2 (Fin n)) :=
    ((X i) ×ˢ (Y i)).image fun q => s(q.1,q.2)
  have inc : G.edgeFinset ⊆ univ.biUnion rect := by
    intro e he
    obtain ⟨i,u,v,hu,hv,rfl⟩ := cover e he
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩
  have localPrice (i : Fin m) : 4 * (rect i).card ≤ 3 * ((X i).card + (Y i).card) := by
    have h : (rect i).card ≤ (X i).card * (Y i).card := by
      simpa only [card_product] using (card_image_le (s := (X i) ×ˢ (Y i))
        (f := fun q : Fin n × Fin n => s(q.1,q.2)))
    exact (Nat.mul_le_mul_left _ h).trans (cleanProductCount G A reg iso girth (X i) (Y i) (clean i)).2
  have price : 4 * G.edgeFinset.card ≤ 3 * ∑ i, ((X i).card + (Y i).card) := by
    calc
      4 * G.edgeFinset.card ≤ 4 * (∑ i, (rect i).card) :=
        Nat.mul_le_mul_left _ ((card_le_card inc).trans card_biUnion_le)
      _ = ∑ i, 4 * (rect i).card := by rw [Finset.mul_sum]
      _ ≤ ∑ i, 3 * ((X i).card + (Y i).card) := sum_le_sum fun i _ => localPrice i
      _ = 3 * ∑ i, ((X i).card + (Y i).card) := by rw [Finset.mul_sum]
  have degrees := cubicDegreeSum G A reg iso
  omega

end PEqualNP.Outside.L_meta_2268_aux.Normal
