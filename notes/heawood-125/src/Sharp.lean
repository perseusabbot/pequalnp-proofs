import Staged

namespace Checkpoint121.Cubic
open Finset SimpleGraph StarUnion
open PEqualNP.Outside.L_meta_2268_aux.Normal

private theorem appendUnion {n} (B : List (Finset (Fin n))) (hb : Built B) (U : Finset (Fin n)) :
    ∃ T, Built T ∧ (∀ a, Ready B a → Ready T a) ∧ Ready T U ∧
      T.length ≤ B.length + (U.card - 1) := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨B,hb,fun _ h => h,Or.inl (by simp),by simp⟩
  | insert a S fresh ih =>
    by_cases empty : S = ∅
    · subst S
      exact ⟨B,hb,fun _ h => h,Or.inl (by simp),by simp⟩
    obtain ⟨T,good,old,read,sz⟩ := ih
    let new := insert a S
    refine ⟨new :: T,⟨good,{a},S,by simp [new],Or.inl (by simp),read⟩,?_,
      Or.inr (List.mem_cons_self ..),?_⟩
    · intro x hx
      rcases old x hx with small | mem
      · exact Or.inl small
      · exact Or.inr (List.mem_cons_of_mem _ mem)
    · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
      rw [Finset.card_insert_of_notMem fresh,List.length_cons]
      omega

private theorem unionFamily {n} {I : Type} [DecidableEq I]
    (Y : I → Finset (Fin n)) (C : Finset I) (inh : ∀ i ∈ C, (Y i).Nonempty) :
    ∃ B, Built B ∧ (∀ i ∈ C, Ready B (Y i)) ∧ B.length + C.card ≤ ∑ i ∈ C, (Y i).card := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨[], trivial, by simp,by simp⟩
  | insert i C fresh ih =>
    obtain ⟨B,good,seen,sz⟩ := ih (fun j hj => inh j (mem_insert_of_mem hj))
    obtain ⟨T,ok,prev,now,len⟩ := appendUnion B good (Y i)
    refine ⟨T,ok,?_,?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | h
      · exact now
      · exact prev _ (seen j h)
    · have pos := card_pos.mpr (inh i (mem_insert_self ..))
      rw [card_insert_of_notMem fresh,sum_insert fresh]
      omega

/-- Assign each edge to one covering endpoint. Each additional leaf of its star
uses one bottom OR. The product for that star uses one middle gate. -/
theorem coverRepresentation {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (V : Finset (Fin n)) (cover : ∀ u v, G.Adj u v → u ∈ V ∨ v ∈ V) :
    ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ (P : List (Finset (Fin n))) a T, B = P ++ a :: T →
        ∃ b c, a = b ∪ c ∧ Ready T b ∧ Ready T c) ∧
      (∀ i, Ready B (X i) ∧ Ready B (Y i)) ∧
      (∀ z, coverTruth X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) ∧
      B.length + 2*m ≤ G.edgeSet.ncard + V.card := by
  classical
  let E := G.edgeFinset
  let c (e : Sym2 (Fin n)) := if e.out.1 ∈ V then e.out.1 else e.out.2
  let l (e : Sym2 (Fin n)) := if e.out.1 ∈ V then e.out.2 else e.out.1
  have oriented (e) : s(c e,l e) = e := by
    by_cases h : e.out.1 ∈ V
    · simpa [c,l,h] using Sym2.mk_fst_out_snd_out e
    · simpa [c,l,h] using (Sym2.eq_swap.trans (Sym2.mk_fst_out_snd_out e) :
        s(e.out.2,e.out.1) = e)
  have adj (e) (he : e ∈ E) : G.Adj (c e) (l e) := by
    have hm : s(c e,l e) ∈ G.edgeFinset := (oriented e).symm ▸ he
    simpa using hm
  let C := E.image c
  have subset : C ⊆ V := by
    rintro _ h
    obtain ⟨e,he,rfl⟩ := mem_image.mp h
    have hc := cover _ _ (adj e he)
    by_cases h : e.out.1 ∈ V <;> simp [c,l,h] at hc ⊢
    exact hc
  let fiber (i : Fin n) := E.filter (fun e => c e = i)
  let leaves (i : Fin n) := (fiber i).image l
  have present (i) (hi : i ∈ C) : (leaves i).Nonempty := by
    obtain ⟨e,he,rfl⟩ := mem_image.mp hi
    exact ⟨l e,mem_image_of_mem _ (mem_filter.mpr ⟨he,rfl⟩)⟩
  obtain ⟨B,built,read,budget⟩ := unionFamily leaves C present
  let src (i : Fin C.card) : Fin n := (C.equivFin.symm i).val
  refine ⟨B,C.card,fun i => {src i},fun i => leaves (src i),?_,?_,?_,?_⟩
  · intro P a T eqn
    exact scheduledAt P a T (eqn ▸ built)
  · exact fun i => ⟨Or.inl (by simp),read _ (C.equivFin.symm i).property⟩
  · intro z
    constructor
    · rintro ⟨i,⟨u,hu,zu⟩,v,hv,zv⟩
      have eq := mem_singleton.mp hu
      obtain ⟨e,he,rfl⟩ := mem_image.mp hv
      obtain ⟨ge,ce⟩ := mem_filter.mp he
      exact ⟨c e,l e,adj e ge,(ce.trans eq.symm) ▸ zu,zv⟩
    · rintro ⟨u,v,uv,zu,zv⟩
      let e := s(u,v)
      have he : e ∈ E := by simpa [e,E] using uv
      let j : C := ⟨c e,mem_image_of_mem _ he⟩
      let i := C.equivFin j
      have source : src i = c e := by simp [src,i,j]
      have both : z (c e) = true ∧ z (l e) = true := by
        rcases Sym2.eq_iff.mp (oriented e) with ⟨p,q⟩ | ⟨p,q⟩ <;> simp_all [e]
      refine ⟨i,⟨c e,by simp [source],both.1⟩,l e,?_,both.2⟩
      change l e ∈ leaves (src i)
      rw [source]
      exact mem_image_of_mem _ (mem_filter.mpr ⟨he,rfl⟩)
  · have count : (∑ i ∈ C, (leaves i).card) ≤ E.card := calc
      _ ≤ ∑ i ∈ C, (fiber i).card := sum_le_sum fun i _ => card_image_le
      _ = E.card := (card_eq_sum_card_image c E).symm
    have size := card_le_card subset
    have coe : G.edgeSet.ncard = E.card := by
      rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
    omega

/-- For square-free graphs, deciding if the representation fits a budget is
exactly the corresponding vertex-cover question. -/
theorem representationIff {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (budget : ℕ) :
    (∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ (P : List (Finset (Fin n))) a T, B = P ++ a :: T →
        ∃ b c, a = b ∪ c ∧ Ready T b ∧ Ready T c) ∧
      (∀ i, Ready B (X i) ∧ Ready B (Y i)) ∧
      (∀ z, coverTruth X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) ∧
      B.length + 2*m ≤ budget) ↔
      ∃ V : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ V ∨ v ∈ V) ∧
        G.edgeSet.ncard + V.card ≤ budget := by
  constructor
  · rintro ⟨B,m,X,Y,build,ready,truth,sz⟩
    obtain ⟨V,cover,h⟩ := PEqualNP.Outside.L_meta_2084_child2 n G girth B m X Y build ready truth
    exact ⟨V,cover,h.trans sz⟩
  · rintro ⟨V,cover,sz⟩
    obtain ⟨B,m,X,Y,build,ready,truth,h⟩ := coverRepresentation G V cover
    exact ⟨B,m,X,Y,build,ready,truth,h.trans sz⟩

#print axioms representationIff
#print axioms coverRepresentation
end Checkpoint121.Cubic
