import BicliqueFormula
import BipartitionCount

namespace PEqualNP.Outside.L_meta_2268_aux.Normal

open Finset

/-- On a bipartite cubic core the star cost lower bound is attained by taking
all three incident edges at each vertex of a color class. -/
theorem exactStarCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (col : G.Colorable 2)
    (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A) :
    ∃ (m : ℕ) (center : Fin m → Fin n) (leaves : Fin m → Finset (Fin n)),
      (∀ i, (leaves i).card = 3) ∧
      (∀ i v, v ∈ leaves i → G.Adj (center i) v) ∧
      (∀ e ∈ G.edgeFinset, ∃ i v, v ∈ leaves i ∧ e = s(center i, v)) ∧
      (∑ i, (leaves i).card) + m - 1 = 2*(n-A.card)-1 := by
  classical
  obtain ⟨T,cov,_,small⟩ := Price.smallCover G A col reg iso
  let S := T \ A
  let center (i : Fin S.card) : Fin n := (S.equivFin.symm i).val
  let leaves (i : Fin S.card) := G.neighborFinset (center i)
  have reg' (i : Fin S.card) : (leaves i).card = 3 := by
    have hi : center i ∈ S := (S.equivFin.symm i).property
    simpa only [leaves,G.card_neighborFinset_eq_degree,← G.ncard_neighborSet] using reg (center i) (mem_sdiff.mp hi).2
  have clean (i : Fin S.card) (v : Fin n) (hv : v ∈ leaves i) : G.Adj (center i) v :=
    (G.mem_neighborFinset _ _).mp hv
  have cover' : ∀ e ∈ G.edgeFinset, ∃ i v, v ∈ leaves i ∧ e = s(center i, v) := by
    intro e
    refine Sym2.ind (fun u v => ?_) e
    intro h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h
    rcases cov u v h with hu | hv
    · let u' : S := ⟨u,mem_sdiff.mpr ⟨hu,iso _ _ h⟩⟩
      refine ⟨S.equivFin u',v,?_,?_⟩
      · simpa [leaves,center,u'] using h
      · simp [center,u']
    · let v' : S := ⟨v,mem_sdiff.mpr ⟨hv,iso _ _ h.symm⟩⟩
      refine ⟨S.equivFin v',u,?_,?_⟩
      · simpa [leaves,center,v'] using h.symm
      · simp [center,v']
  refine ⟨S.card,center,leaves,reg',clean,cover',?_⟩
  have size : (∑ i, (leaves i).card) = 3*S.card := by simp [reg', Nat.mul_comm]
  have lower := starFormulaLower G A reg iso center leaves clean cover'
  have deg := cubicDegreeSum G A reg iso
  have card : S.card ≤ T.card := card_le_card sdiff_subset
  omega


/-- The same optimum is attained among products of two variable disjunctions. -/
theorem exactBicliqueCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (col : G.Colorable 2)
    (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A) :
    ∃ (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ i u, u ∈ X i → ∀ v, v ∈ Y i → G.Adj u v) ∧
      (∀ e ∈ G.edgeFinset, ∃ i u v, u ∈ X i ∧ v ∈ Y i ∧ e = s(u,v)) ∧
      (∑ i, ((X i).card + (Y i).card)) - 1 = 2*(n-A.card)-1 := by
  classical
  obtain ⟨m,center,leaves,_,clean,cover,price⟩ := exactStarCover G A col reg iso
  refine ⟨m,(fun i => {center i}),leaves,?_,?_,?_⟩
  · intro i u hu v hv
    exact (Finset.mem_singleton.mp hu) ▸ clean i v hv
  · intro e he
    obtain ⟨i,v,hv,h⟩ := cover e he
    exact ⟨i,center i,v,mem_singleton_self _,hv,h⟩
  · simpa [Finset.sum_add_distrib,Nat.add_comm] using price

end PEqualNP.Outside.L_meta_2268_aux.Normal
