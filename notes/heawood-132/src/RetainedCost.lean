import SpecificSupports

namespace Checkpoint132.Retained
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open Checkpoint125.Certificate Checkpoint126 Checkpoint128.Heawood Checkpoint129.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Retain the actual number of regular bottom gates in the cost of a boundary projection.
Each distinct product in the output pays once in the original book and once when its label is erased. -/
theorem projectedAvailable {A R : Type} [DecidableEq A] (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (rows : R→V→Bool) (pos : ∃ r,predicate (rows r))
    (boundary : ∀ r,BoundaryRow ((run 14 gs).wires.getD out default) (rows r))
    (portMap : Support 14→Option A) (signal : R→A→Prop)
    (agree : ∀ r S, (S.card≤1 ∨ S∈kept (survivors ((run 14 gs).wires.getD out default)) (run 14 gs).bottom) →
      ((portMap S).elim False (signal r) ↔ lit S (rows r))) :
    let s := run 14 gs
    let w := s.wires.getD out default
    ∃ book : List (Binary.Tree A), ∃ t, Binary.Built book ∧ Binary.Ready book t ∧
      (∀ r,t.eval (signal r) ↔ predicate (rows r)) ∧
      (kept (survivors w) s.bottom).length+2*w.jobs.card+book.length≤gs.length := by
  classical
  let s := run 14 gs
  let w := s.wires.getD out default
  let H := survivors w
  let bank := kept H s.bottom
  have original (S : Support 14) (mem : S∈s.bottom) : Bank.Allowed bank S ↔ Regular H S := by
    constructor
    · rintro (tiny|listed)
      · exact Or.inl tiny
      · exact of_decide_eq_true (List.mem_filter.mp listed).2
    · exact fun reg => Or.inr (List.mem_filter.mpr ⟨mem,decide_eq_true reg⟩)
  have discarded : Bank.discard bank s.bottom=waste H s.bottom := by
    unfold Bank.discard waste
    apply congrArg List.length
    apply List.filter_congr
    intro S h
    exact congrArg Bool.not (decide_eq_decide.mpr (original S h))
  obtain ⟨book,e,built,ready,faith,count⟩ := Bank.circuitBook bank w.jobs gs out
  have valid := (run_valid 14 gs).1
  have sound (z) (hz : accepts w z) := (spec z).mp ((port valid out).sound z hz)
  have products := chargeProducts valid out
  have spentAll := (run_valid 14 gs).2
  have split := List.length_eq_countP_add_countP (l:=s.bottom) (fun v => decide (Regular H v))
  simp only [List.countP_eq_length_filter] at split
  change s.bottom.length=(kept H s.bottom).length+waste H s.bottom at split
  change w.jobs.card+extra w.jobs s ≤ s.products.length+s.bypass at products
  change s.bottom.length+s.top.length+s.products.length+s.dropped+s.bypass=gs.length at spentAll
  change book.length=Bank.discard bank s.bottom+extra w.jobs s+s.dropped+s.top.length at count
  rw [discarded] at count
  let f : Label→Option A := Sum.elim portMap (fun _ => none)
  let dead := e.vars.filter (fun l => f l=none)
  have included : w.jobs.image (Sum.inr : Product 14→Label) ⊆ dead := by
    intro l hl
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hl
    exact mem_filter.mpr ⟨faith.roots p hp hp,rfl⟩
  have price := card_le_card included
  rw [card_image_of_injective _ Sum.inr_injective] at price
  have truth (r) : Zero.value (signal r) (Zero.reduce f e) ↔ predicate (rows r) := by
    have atLeaf (l : Label) (hl : l∈e.vars) : (f l).elim False (signal r) ↔ interpret (rows r) l := by
      cases l with
      | inl v => exact agree r v (faith.regular v hl)
      | inr j => rfl
    exact (Zero.semantics f _ e).trans ((Iff.intro (e.mono (fun l h => (atLeaf l h).mp))
      (e.mono (fun l h => (atLeaf l h).mpr))).trans
      ((faith.exactOn _ (boundaryDomain sound (boundary r))).trans (spec (rows r))))
  cases eq : Zero.reduce f e with
  | none =>
    obtain ⟨r,yes⟩ := pos
    have fail := (truth r).mpr yes
    simp [eq,Zero.value] at fail
  | some t =>
    obtain ⟨ok,reached⟩ := Zero.library f built
    have pay := Zero.cost f built ready eq
    change (book.filterMap (Zero.emit f)).length+dead.card≤book.length at pay
    refine ⟨_,t,ok,reached e ready t eq,fun r => by simpa [eq,Zero.value] using truth r,?_⟩
    change (kept H s.bottom).length+2*w.jobs.card+_≤gs.length
    omega

/-- A boundary calculation may also grant every regular support of the retained graph. -/
theorem projectedCost {A R : Type} [DecidableEq A] (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (rows : R→V→Bool) (pos : ∃ r,predicate (rows r))
    (boundary : ∀ r,BoundaryRow ((run 14 gs).wires.getD out default) (rows r))
    (portMap : Support 14→Option A) (signal : R→A→Prop)
    (agree : ∀ r S,Regular (survivors ((run 14 gs).wires.getD out default)) S →
      ((portMap S).elim False (signal r) ↔ lit S (rows r))) :
    let s := run 14 gs
    let w := s.wires.getD out default
    ∃ book : List (Binary.Tree A), ∃ t, Binary.Built book ∧ Binary.Ready book t ∧
      (∀ r,t.eval (signal r) ↔ predicate (rows r)) ∧
      (kept (survivors w) s.bottom).length+2*w.jobs.card+book.length≤gs.length := by
  apply projectedAvailable gs out spec rows pos boundary portMap signal
  intro r S h
  exact agree r S (h.elim Or.inl (fun mem => of_decide_eq_true (List.mem_filter.mp mem).2))

#print axioms projectedAvailable
#print axioms projectedCost
end Checkpoint132.Retained
