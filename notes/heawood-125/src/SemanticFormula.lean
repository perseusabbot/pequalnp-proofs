import ExactCleanFormula

namespace PEqualNP.Outside.L_meta_2268_aux.Normal

open Finset

/-- Boolean truth condition for an OR of products of two input disjunctions. -/
def coverTruth {n m : ℕ} (X Y : Fin m → Finset (Fin n)) (z : Fin n → Bool) : Prop :=
  ∃ i, (∃ u ∈ X i, z u = true) ∧ (∃ v ∈ Y i, z v = true)

/-- Truth on singleton and two-vertex inputs recovers cleanliness and coverage
for a positive formula that computes the edge function. -/
theorem cleanCoverOfSemantics {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Y : Fin m → Finset (Fin n))
    (computes : ∀ z, coverTruth X Y z ↔
      ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) :
    (∀ i u, u ∈ X i → ∀ v, v ∈ Y i → G.Adj u v) ∧
    (∀ e ∈ G.edgeFinset, ∃ i u v, u ∈ X i ∧ v ∈ Y i ∧ e = s(u,v)) := by
  classical
  let pair (u v w : Fin n) := decide (w = u ∨ w = v)
  have pairTrue (u v w : Fin n) : pair u v w = true ↔ w = u ∨ w = v := by simp [pair]
  have clean (i : Fin m) (u : Fin n) (hu : u ∈ X i) (v : Fin n) (hv : v ∈ Y i) :
      G.Adj u v := by
    have yes : coverTruth X Y (pair u v) :=
      ⟨i,⟨u,hu,(pairTrue u v u).mpr (Or.inl rfl)⟩,⟨v,hv,(pairTrue u v v).mpr (Or.inr rfl)⟩⟩
    obtain ⟨a,b,ab,ha,hb⟩ := (computes _).mp yes
    rcases (pairTrue u v a).mp ha with rfl | rfl <;>
      rcases (pairTrue _ _ b).mp hb with rfl | rfl
    · exact False.elim (G.irrefl ab)
    · exact ab
    · exact ab.symm
    · exact False.elim (G.irrefl ab)
  refine ⟨clean,?_⟩
  intro e
  refine Sym2.ind (fun u v => ?_) e
  intro h
  rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at h
  have yes := (computes (pair u v)).mpr
    ⟨u,v,h,(pairTrue u v u).mpr (Or.inl rfl),(pairTrue u v v).mpr (Or.inr rfl)⟩
  obtain ⟨i,⟨a,ha,pa⟩,⟨b,hb,pb⟩⟩ := yes
  refine ⟨i,a,b,ha,hb,?_⟩
  have ne := (clean i a ha b hb).ne
  rcases (pairTrue u v a).mp pa with rfl | rfl <;>
    rcases (pairTrue _ _ b).mp pb with rfl | rfl
  · exact False.elim (ne rfl)
  · rfl
  · exact Sym2.eq_swap
  · exact False.elim (ne rfl)

/-- Every unshared formula of this syntax computing the graph function
obeys the benchmark, even without explicit cleanliness/coverage assumptions. -/
theorem semanticFormulaLower {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A)
    (girth : ∀ z (p : G.Walk z z), p.IsCycle → 5 ≤ p.length)
    (X Y : Fin m → Finset (Fin n))
    (computes : ∀ z, coverTruth X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) :
    2 * (n - A.card) - 1 ≤ (∑ i, ((X i).card + (Y i).card)) - 1 := by
  obtain ⟨clean,cover⟩ := cleanCoverOfSemantics G X Y computes
  exact bicliqueFormulaLower G A reg iso girth X Y clean cover


theorem semanticsOfCleanCover {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Y : Fin m → Finset (Fin n))
    (clean : ∀ i u, u ∈ X i → ∀ v, v ∈ Y i → G.Adj u v)
    (cover : ∀ e ∈ G.edgeFinset, ∃ i u v, u ∈ X i ∧ v ∈ Y i ∧ e = s(u,v))
    (z : Fin n → Bool) :
    coverTruth X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true := by
  constructor
  · rintro ⟨i,⟨u,hu,zu⟩,⟨v,hv,zv⟩⟩
    exact ⟨u,v,clean i u hu v hv,zu,zv⟩
  · rintro ⟨u,v,adj,zu,zv⟩
    obtain ⟨i,a,b,ha,hb,h⟩ := cover s(u,v) (by simpa using adj)
    rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨i,⟨_,ha,zu⟩,⟨_,hb,zv⟩⟩
    · exact ⟨i,⟨_,ha,zv⟩,⟨_,hb,zu⟩⟩

/-- Existence of a formula with the stated semantics and exactly the optimum
number of unshared binary gates. -/
theorem semanticFormulaAttains {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (col : G.Colorable 2)
    (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A) :
    ∃ (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ z, coverTruth X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) ∧
      (∑ i, ((X i).card + (Y i).card)) - 1 = 2*(n-A.card)-1 := by
  obtain ⟨m,X,Y,clean,cover,price⟩ := exactBicliqueCover G A col reg iso
  exact ⟨m,X,Y,semanticsOfCleanCover G X Y clean cover,price⟩

end PEqualNP.Outside.L_meta_2268_aux.Normal
