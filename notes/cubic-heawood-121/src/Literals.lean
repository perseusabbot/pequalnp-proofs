import L_meta_2535

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2535_aux

namespace PEqualNP.Outside.L_meta_2268_aux.Literals

theorem appendOne {n s : ℕ} (i : Fin n) {f : (Fin n → Bool) → Bool}
    (h : HasCircuitSize n f s) :
    HasCircuitSize n (fun x => x i || f x) (s+1) := by
  obtain ⟨C,legal,size,correct⟩ := h
  let g : Gate := ⟨GateOp.or,[i.val,C.output]⟩
  refine ⟨⟨C.gates ++ [g], n+C.gates.length⟩, ?_, ?_, ?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact legal z hz
    · obtain rfl : z = g := by simpa using hz
      simp [g]
  · change (C.gates ++ [g]).length ≤ s+1
    simpa [Circuit.size] using Nat.add_le_add_right size 1
  · intro x
    let w := wiresFrom C.gates (List.ofFn x)
    have len : w.length = n+C.gates.length := by simp [w,length_wiresFrom]
    have left : w.getD i.val false = x i := by
      rw [show w = wiresFrom C.gates (List.ofFn x) from rfl,getD_wiresFrom _ _ _ (by simp)]
      exact getD_ofFn_lt _ _ _ i.isLt
    have right : w.getD C.output false = f x := correct x
    change (wiresFrom (C.gates ++ [g]) (List.ofFn x)).getD (n+C.gates.length) false = _
    rw [wiresFrom_append]
    change (w ++ [GateOp.or.eval [w.getD i.val false,w.getD C.output false]]).getD (n+C.gates.length) false = _
    rw [← len,getD_snoc_eq,left,right]
    simp [GateOp.eval]

theorem appendSet {n t : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n f t) :
    HasCircuitSize n (fun x => decide (∃ v ∈ A, x v = true) || f x) (t+A.card) := by
  induction A using Finset.induction_on with
  | empty => simpa using h
  | @insert i A hi ih =>
    have next := appendOne i ih
    convert next using 1
    · funext x
      apply Bool.eq_iff_iff.mpr
      simp [or_assoc]
    · rw [Finset.card_insert_of_notMem hi]; omega

private theorem graph_spec {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (x : Fin n → Bool) : graphFun G A x = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

private theorem graph_zero {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) :
    graphFun G A (fun _ => false) = false := by simp [graphFun]

private theorem pin_literal {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (i : Fin n) (hi : i ∉ A)
    (isolated : ∀ u v, G.Adj u v → u ≠ i) (x : Fin n → Bool) :
    graphFun G (insert i A) (Function.update x i false) = graphFun G A x := by
  apply Bool.eq_iff_iff.mpr
  rw [graph_spec,graph_spec]
  have ha {a} (mem : a ∈ A) : Function.update x i false a = x a :=
    Function.update_of_ne (show a ≠ i by intro e; subst a; exact hi mem) ..
  have hE {u v} (edge : G.Adj u v) : Function.update x i false u = x u ∧
      Function.update x i false v = x v :=
    ⟨Function.update_of_ne (isolated u v edge) ..,Function.update_of_ne (isolated v u edge.symm) ..⟩
  constructor
  · rintro (⟨a,mem,h⟩ | ⟨u,v,edge,hu,hv⟩)
    · rcases Finset.mem_insert.mp mem with rfl | mem
      · simp at h
      · exact Or.inl ⟨a,mem,(ha mem) ▸ h⟩
    · exact Or.inr ⟨u,v,edge,(hE edge).1 ▸ hu,(hE edge).2 ▸ hv⟩
  · rintro (⟨a,mem,h⟩ | ⟨u,v,edge,hu,hv⟩)
    · exact Or.inl ⟨a,Finset.mem_insert_of_mem mem,(ha mem).symm ▸ h⟩
    · exact Or.inr ⟨u,v,edge,(hE edge).1.symm ▸ hu,(hE edge).2.symm ▸ hv⟩

private theorem positive_budget {n s} (i : Fin n) (f : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n f s)
    (dep : ∃ x, f (Function.update x i false) ≠ f (Function.update x i true))
    (nc : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false)) : 0 < s := by
  by_contra! hz
  obtain ⟨⟨gs,o⟩,_,size,corr⟩ := h
  have gl : gs.length = 0 := by change gs.length ≤ s at size; omega
  obtain rfl : gs = [] := List.length_eq_zero_iff.mp gl
  change ∀ x, (List.ofFn x).getD o false = f x at corr
  by_cases ho : o < n
  · let j : Fin n := ⟨o,ho⟩
    have eq (x : Fin n → Bool) : f x = x j := (corr x).symm.trans (getD_ofFn_lt _ _ _ ho)
    by_cases same : j=i
    · obtain ⟨x,y,d⟩ := nc
      exact d (by rw [eq,eq,same]; simp)
    · obtain ⟨x,d⟩ := dep
      exact d (by rw [eq,eq,Function.update_of_ne same,Function.update_of_ne same])
  · obtain ⟨x,d⟩ := dep
    apply d
    rw [← corr,← corr,getD_ofFn_ge _ _ _ (by omega),getD_ofFn_ge _ _ _ (by omega)]

theorem strip {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (isolated : ∀ u v, G.Adj u v → u ∉ A) (edge : ∃ u v, G.Adj u v)
    {s} (h : HasCircuitSize n (graphFun G A) s) :
    ∃ t, t+A.card ≤ s ∧ HasCircuitSize n (graphFun G ∅) t := by
  induction A using Finset.induction_on generalizing s with
  | empty => exact ⟨s,by simp,h⟩
  | @insert i A hi ih =>
    have hI : ∀ u v, G.Adj u v → u ≠ i := by
      intro u v adj e
      exact isolated u v adj (Finset.mem_insert.mpr (Or.inl e))
    have old : ∀ u v, G.Adj u v → u ∉ A := by
      intro u v adj m
      exact isolated u v adj (Finset.mem_insert_of_mem m)
    have dep : ∃ x, graphFun G (insert i A) (Function.update x i false) ≠
        graphFun G (insert i A) (Function.update x i true) := by
      refine ⟨fun _ => false,?_⟩
      rw [pin_literal G A i hi hI,graph_zero]
      have ok : graphFun G (insert i A) (Function.update (fun _ => false) i true) = true :=
        (graph_spec ..).2 (Or.inl ⟨i,Finset.mem_insert_self ..,Function.update_self ..⟩)
      simp [ok]
    have nc : ∃ x y, graphFun G (insert i A) (Function.update x i false) ≠
        graphFun G (insert i A) (Function.update y i false) := by
      refine ⟨fun _ => false,fun _ => true,?_⟩
      rw [pin_literal G A i hi hI,pin_literal G A i hi hI,graph_zero]
      obtain ⟨u,v,uv⟩ := edge
      have ok : graphFun G A (fun _ => true) = true := (graph_spec ..).2 (Or.inr ⟨u,v,uv,rfl,rfl⟩)
      simp [ok]
    have pos := positive_budget i _ h dep nc
    have pin := PEqualNP.Outside.L_meta_2535 n s _ i h dep nc
    have eq : (fun x => graphFun G (insert i A) (Function.update x i false)) = graphFun G A :=
      funext (pin_literal G A i hi hI)
    rw [eq] at pin
    obtain ⟨t,le,size⟩ := ih old pin
    exact ⟨t,by rw [Finset.card_insert_of_notMem hi]; omega,size⟩

/-- Independent positive inputs add one gate each to the minimum of a nonempty graph. -/
theorem exactLiteralCost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (isolated : ∀ u v, G.Adj u v → u ∉ A) (edge : ∃ u v, G.Adj u v)
    (s : ℕ) : HasCircuitSize n (graphFun G A) s ↔
      ∃ t, t + A.card ≤ s ∧ HasCircuitSize n (graphFun G ∅) t := by
  refine ⟨strip G A isolated edge, ?_⟩
  rintro ⟨t,le,h⟩
  obtain ⟨C,legal,size,correct⟩ := appendSet A (graphFun G ∅) h
  refine ⟨C,legal,size.trans le,?_⟩
  intro x
  simpa [graphFun] using correct x

#print axioms exactLiteralCost
#print axioms strip
#print axioms appendSet
end PEqualNP.Outside.L_meta_2268_aux.Literals
