import Fooling

namespace Checkpoint140

open Finset PEqualNP.Outside.L_meta_9338

/-- Any color class whose crossed entries are all zero gives a legal Cartesian product. -/
theorem colorsCover (U : Finset (V × V)) (k : ℕ) :
    (∃ f : U → Fin k, ∀ x y : U, f x = f y → bit x.val.1 y.val.2 = false) ↔
    (∃ b : Fin k → Box, (∀ i, legal (b i)) ∧ ∀ x : U, ∃ i, hit (b i) x.val.1 x.val.2) := by
  classical
  constructor
  · rintro ⟨f,ok⟩
    let rows (i : Fin k) := univ.filter (fun p : V => ∃ x : U, f x = i ∧ x.val.1 = p)
    let cols (i : Fin k) := univ.filter (fun q : V => ∃ x : U, f x = i ∧ x.val.2 = q)
    refine ⟨fun i => (rows i,cols i),?_,?_⟩
    · intro i p hp q hq
      obtain ⟨x,hx,rfl⟩ := (mem_filter.mp hp).2
      obtain ⟨y,hy,rfl⟩ := (mem_filter.mp hq).2
      exact ok x y (hx.trans hy.symm)
    · intro x
      exact ⟨f x,mem_filter.mpr ⟨mem_univ _,x,rfl,rfl⟩,mem_filter.mpr ⟨mem_univ _,x,rfl,rfl⟩⟩
  · rintro ⟨b,legalB,cover⟩
    choose f hitF using cover
    refine ⟨f,fun x y same => ?_⟩
    exact legalB (f x) _ (hitF x).1 _ (same.symm ▸ (hitF y).2)

#print axioms colorsCover

end Checkpoint140
