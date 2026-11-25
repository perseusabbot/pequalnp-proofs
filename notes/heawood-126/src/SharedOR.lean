import SemanticFormula
import StarUnion

namespace PEqualNP.Outside.L_meta_2268_aux.Normal

open Finset StarUnion

/-- A single binary OR output reaching s distinct inputs needs at least s−1 OR gates.
Its gate schedule can have arbitrary fanout and may also contain unused entries. -/
theorem collectorBound {V : Type} [DecidableEq V] (gs : List (Finset V))
    (built : Built gs) (S : Finset V) (out : Ready gs S) : S.card ≤ gs.length + 1 := by
  classical
  have reach := cover gs built {S} S (by simpa using out) (by simp)
  have price (l : List (Finset V)) : charge S l ≤ l.length := by
    induction l with
    | nil => simp [charge]
    | cons a l ih =>
      simp only [charge, List.length_cons]
      split <;> omega
  have := price gs
  simp only [card_singleton] at reach
  omega

/-- Only AND outputs in the support of the top OR output contribute to its truth value. -/
def reachableTruth {n m : ℕ} (S : Finset (Fin m)) (X Y : Fin m → Finset (Fin n))
    (z : Fin n → Bool) : Prop :=
  ∃ i ∈ S, (∃ u ∈ X i, z u = true) ∧ (∃ v ∈ Y i, z v = true)

/-- Abstract three-stage circuit with arbitrary sharing in both OR stages. The bottom
schedule builds positive OR supports. The m middle gates take binary ANDs. The top
schedule builds ORs of middle-gate indices. S is the support of its selected output.
Only distinct reachable indices are charged. -/
theorem sharedORLower {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A)
    (girth : ∀ z (p : G.Walk z z), p.IsCycle → 5 ≤ p.length)
    (bottom : List (Finset (Fin n))) (botOK : Built bottom)
    (X Y : Fin m → Finset (Fin n)) (availableX : ∀ i, Ready bottom (X i))
    (availableY : ∀ i, Ready bottom (Y i))
    (top : List (Finset (Fin m))) (topOK : Built top)
    (S : Finset (Fin m)) (out : Ready top S)
    (computes : ∀ z, reachableTruth S X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) :
    2*(n-A.card) - 1 ≤ bottom.length + m + top.length := by
  classical
  let e := S.equivFin
  let src (i : Fin S.card) : Fin m := (e.symm i).val
  let U (i : Fin S.card) := X (src i)
  let W (i : Fin S.card) := Y (src i)
  have yes (z : Fin n → Bool) : coverTruth U W z ↔ reachableTruth S X Y z := by
    constructor
    · rintro ⟨i,hu,hw⟩
      exact ⟨src i,(e.symm i).property,hu,hw⟩
    · rintro ⟨i,hi,hu,hw⟩
      let j : S := ⟨i,hi⟩
      exact ⟨e j,by simpa [U,src,j] using hu,by simpa [W,src,j] using hw⟩
  obtain ⟨clean,covered⟩ := cleanCoverOfSemantics G U W fun z => (yes z).trans (computes z)
  have square : NoSquare G := by
    intro i k j l ik ij kj il kl
    by_contra jl
    exact noSquare G girth ij kj.symm kl il.symm ik jl
  have lower := rectangleEdges G square bottom botOK (univ : Finset (Fin S.card)) U W
    (fun i _ => availableX (src i)) (fun i _ => availableY (src i))
    (fun i _ => clean i) G.edgeFinset (by
      intro edge h
      obtain ⟨i,u,v,hu,hv,eq⟩ := covered edge h
      exact ⟨i,mem_univ _,u,hu,v,hv,eq⟩)
  simp only [card_univ, Fintype.card_fin] at lower
  let parts (i : Fin S.card) : Finset (Sym2 (Fin n)) :=
    ((U i) ×ˢ (W i)).image fun q => s(q.1,q.2)
  have inc : G.edgeFinset ⊆ univ.biUnion parts := by
    intro edge he
    obtain ⟨i,u,v,hu,hv,rfl⟩ := covered edge he
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩
  have upper : G.edgeFinset.card ≤ 3*S.card := by
    calc
      G.edgeFinset.card ≤ ∑ i, (parts i).card := (card_le_card inc).trans card_biUnion_le
      _ ≤ ∑ _i : Fin S.card, 3 := by
        apply sum_le_sum
        intro i _
        have h : (parts i).card ≤ (U i).card * (W i).card := by
          simpa only [card_product] using (card_image_le (s := (U i) ×ˢ (W i))
            (f := fun q : Fin n × Fin n => s(q.1,q.2)))
        exact h.trans (cleanProductCount G A reg iso girth (U i) (W i) (clean i)).1
      _ = 3*S.card := by simp [Nat.mul_comm]
  have deg := cubicDegreeSum G A reg iso
  have topCost := collectorBound top topOK S out
  have active : S.card ≤ m := by simpa only [Fintype.card_fin] using card_le_univ S
  omega

end PEqualNP.Outside.L_meta_2268_aux.Normal
