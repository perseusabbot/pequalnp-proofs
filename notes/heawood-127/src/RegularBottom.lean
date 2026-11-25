import PrunedEdges

namespace Checkpoint124.Heawood
open Finset SimpleGraph StarUnion Checkpoint122.Pruning
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- An input, constant zero, or an OR support supplied by one retained neighborhood. -/
def Regular (H : Finset (Sym2 V)) (S : Support 14) : Prop :=
  S.card≤1 ∨ ∃ c : V, ∀ u∈S, s(c,u)∈H

instance {H S} : Decidable (Regular H S) := by unfold Regular; infer_instance

theorem regularSubset {H S U} (hs : Regular H S) (sub : U⊆S) : Regular H U :=
  hs.elim (fun h => Or.inl ((card_le_card sub).trans h))
    (fun ⟨c,h⟩ => Or.inr ⟨c,fun u hu => h u (sub hu)⟩)

def kept (H : Finset (Sym2 V)) (B : List (Support 14)) := B.filter (fun S => decide (Regular H S))
def waste (H : Finset (Sym2 V)) (B : List (Support 14)) := (B.filter (fun S => !decide (Regular H S))).length

private theorem stillReady {H S B} (ready : Ready B S) (ok : Regular H S) : Ready (kept H B) S :=
  ready.imp_right (fun h => List.mem_filter.mpr ⟨h,decide_eq_true ok⟩)

theorem keptBuilt {H} (B : List (Support 14)) (h : Built B) : Built (kept H B) := by
  induction B with
  | nil => trivial
  | cons a B ih =>
    obtain ⟨prev,x,y,rfl,rx,ry⟩ := h
    by_cases ok : Regular H (x∪y)
    · rw [show kept H ((x∪y)::B) = (x∪y)::kept H B by simp [kept,ok]]
      exact ⟨ih prev,x,y,rfl,stillReady rx (regularSubset ok subset_union_left),
        stillReady ry (regularSubset ok subset_union_right)⟩
    · simpa [kept,ok] using ih prev

theorem squareFree : NoSquare G := by
  intro i j a b ij ia ja ib jb
  by_contra ab
  exact PEqualNP.Outside.L_meta_2268_aux.Normal.noSquare G
    (fun u p h => by have := girth_six u p h; omega) ia ja.symm jb ib.symm ij ab

/-- Each OR gate outside all retained neighborhoods costs a gate beyond the rectangle bound. -/
theorem chargedBottom {w : Wire 14} (B : List (Support 14)) (ok : Built B)
    (ready : ∀ p∈w.jobs, Ready B p.1 ∧ Ready B p.2)
    (sound : ∀ z, accepts w z → predicate z) :
    (survivors w).card + waste (survivors w) B ≤ w.jobs.card + B.length := by
  classical
  let H := survivors w
  let J := w.jobs.filter (fun p => p.1.Nonempty ∧ p.2.Nonempty)
  have fits {p : Product 14} (hp : p∈J) : Ready (kept H B) p.1 ∧ Ready (kept H B) p.2 := by
    obtain ⟨h,⟨a,ha⟩,⟨b,hb⟩⟩ := mem_filter.mp hp
    refine ⟨stillReady (ready _ h).1 (Or.inr ⟨b,fun u hu => ?_⟩),
      stillReady (ready _ h).2 (Or.inr ⟨a,fun v hv => ?_⟩)⟩
    · exact (in_survivors w _).mpr ⟨p,h,u,hu,b,hb,Sym2.eq_swap⟩
    · exact (in_survivors w _).mpr ⟨p,h,a,ha,v,hv,rfl⟩
  have cover := rectangleEdges G squareFree (kept H B) (keptBuilt B ok) J Prod.fst Prod.snd
    (fun _ hp => (fits hp).1) (fun _ hp => (fits hp).2)
    (fun p hp => (describe sound).2 p (mem_filter.mp hp).1) H (by
      intro e he
      obtain ⟨p,hp,a,ha,b,hb,rfl⟩ := (in_survivors w e).mp he
      exact ⟨p,mem_filter.mpr ⟨hp,⟨a,ha⟩,⟨b,hb⟩⟩,a,ha,b,hb,rfl⟩)
  have count := List.length_eq_countP_add_countP (l:=B) (fun S => decide (Regular H S))
  simp only [List.countP_eq_length_filter] at count
  have split : B.length=(kept H B).length+waste H B := count
  have cap : J.card ≤ w.jobs.card := card_filter_le ..
  change H.card+waste H B ≤ w.jobs.card+B.length
  omega

def extra {n} (J : Finset (Product n)) (s : State n) :=
  (s.products.filter (fun p => decide (p∉J))).length+s.bypass

theorem chargeProducts {s : State 14} (valid : Valid s) (out : ℕ) :
    (s.wires.getD out default).jobs.card+extra (s.wires.getD out default).jobs s ≤
      s.products.length+s.bypass := by
  let J := (s.wires.getD out default).jobs
  let live := s.products.filter (fun p => decide (p∈J))
  have sub : J ⊆ live.toFinset := fun p hp => List.mem_toFinset.mpr
    (List.mem_filter.mpr ⟨(port valid out).owned _ hp,decide_eq_true hp⟩)
  have cap := (card_le_card sub).trans live.toFinset_card_le
  have split := List.length_eq_countP_add_countP (l:=s.products) (fun p => decide (p∈J))
  simp only [List.countP_eq_length_filter] at split
  change J.card+((s.products.filter (fun p => decide (p∉J))).length+s.bypass)≤_
  change J.card≤(s.products.filter (fun p => decide (p∈J))).length at cap
  have total : s.products.length = (s.products.filter (fun p => decide (p∈J))).length +
      (s.products.filter (fun p => decide (p∉J))).length := by simpa using split
  omega

#print axioms chargedBottom
#print axioms chargeProducts
end Checkpoint124.Heawood
