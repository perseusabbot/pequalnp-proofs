import EdgeSeparation
import ResidualCircuit

namespace Checkpoint124.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Library Checkpoint124.Shapes
open PEqualNP.Outside.L_meta_3004_aux.Controls

def price (gs : List Op) (out : ℕ) :=
  let s := run 14 gs
  let w := s.wires.getD out default
  events (survivors w) w.jobs s

/-- Every retained edge, every surviving product and every counted exceptional
gate can be charged within the actual gate budget. -/
theorem priceBudget (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (mark : none∈((run 14 gs).wires.getD out default).tags) :
    let w := (run 14 gs).wires.getD out default
    (survivors w).card+w.jobs.card+price gs out≤gs.length := by
  let s := run 14 gs
  let w := s.wires.getD out default
  obtain ⟨valid,cost⟩ := run_valid 14 gs
  have fw := port valid out
  have sound (z) (h : accepts w z) := (spec z).mp (fw.sound _ h)
  have bottom := chargedBottom s.bottom valid.bottom (fun p hp => valid.operands _ (fw.owned p hp)) sound
  change (survivors w).card+waste (survivors w) s.bottom ≤ w.jobs.card+s.bottom.length at bottom
  have products := chargeProducts valid out
  have high := (budget valid out spec).top
  change w.jobs.card+extra w.jobs s ≤ s.products.length+s.bypass at products
  change w.tags.card ≤ s.top.length+1 at high
  have tags := card_eraseNone_of_mem mark
  change w.jobs.card=w.tags.card-1 at tags
  have nonempty := card_pos.mpr (show w.tags.Nonempty from ⟨none,mark⟩)
  change s.bottom.length+s.top.length+s.products.length+s.dropped+s.bypass=gs.length at cost
  change (survivors w).card+w.jobs.card+(waste (survivors w) s.bottom+extra w.jobs s+s.dropped)≤gs.length
  omega

/-- On inputs rejected by pruning, full correctness needs at least one
regular conjunction per missing edge. The finite relaxation supplies the terms. -/
theorem residualTerms (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (mark : none∈((run 14 gs).wires.getD out default).tags) :
    let w := (run 14 gs).wires.getD out default
    ∃ q∈frames (price gs out), q.cut=true ∧ ∃ f∈q.pool, missed w≤f.length := by
  let s := run 14 gs
  let w := s.wires.getD out default
  let X := {z : V → Bool // ¬accepts w z}
  let xs : X → (V → Bool) := Subtype.val
  have valid : Valid s := (run_valid 14 gs).1
  have fw := port valid out
  have sound (z) (h : accepts w z) := (spec z).mp (fw.sound _ h)
  have imp : w.pure=false := by
    cases hp : w.pure with
    | false => rfl
    | true =>
      have empty : w.tags=∅ := fw.empty hp
      exact False.elim (notMem_empty _ (empty ▸ mark))
  have dead (p) (hp : p∈w.jobs) : signal xs p.1 ∩ signal xs p.2=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun x h => x.property (Or.inr ⟨p,hp,h⟩)
  obtain ⟨c,cut,rep⟩ := representation (survivors w) w.jobs xs gs dead out imp
  obtain ⟨f,hf,real⟩ := rep
  refine ⟨c.q,c.reachable,cut.mpr (fw.marked mark),f,hf,?_⟩
  let feature := fun i => c.bank.getD i (default : Sources)
  have regular (i) : Regular (survivors w) (feature i) := by
    by_cases good : i<c.bank.length
    · unfold feature
      rw [List.getD_eq_getElem _ _ good]
      exact c.regular c.bank[i] (List.getElem_mem ..)
    · rw [show feature i=∅ from by unfold feature; rw [List.getD_eq_default _ _ (by omega)]; rfl]
      exact Or.inl (by simp)
  apply restorationBound w (budget valid out spec).sub sound feature regular f
  intro z no
  let x : X := ⟨z,no⟩
  have sets : eval (fun i => signal xs (feature i)) f=value xs w := by
    simpa only [List.append_nil] using real []
  have hx := Set.ext_iff.mp sets x
  change (∃ t∈f, ∀ a∈t, lit (feature a) z) ↔ w.full z=true at hx
  exact (spec z).symm.trans hx.symm

#print axioms priceBudget
#print axioms residualTerms
end Checkpoint124.Heawood
