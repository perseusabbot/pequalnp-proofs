import TenLossFloor

namespace Checkpoint128.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open Checkpoint126 PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Missing individual edge inputs and negative assignments are both in the
domain on which every retained ordinary product is false. -/
def BoundaryRow (w : Wire 14) (z : V→Bool) :=
  (∃ i∈lost w, z=positive i) ∨ ¬predicate z

theorem boundaryDomain {w : Wire 14} (sound : ∀ z,accepts w z → predicate z)
    {z} (row : BoundaryRow w z) : Domain w.jobs z := by
  rintro p hp hit
  have yes : accepts w z := Or.inr ⟨p,hp,hit⟩
  rcases row with ⟨i,hi,rfl⟩|negative
  · exact (mem_filter.mp hi).2 ((survives_iff sound _ _).mpr yes)
  · exact negative (sound _ yes)

/-- Any exact interpretation of the regular disjunction inputs on the chosen
boundary rows yields a residual circuit within the original gate count less
the surviving edges and the distinct retained products. -/
theorem boundaryCircuit {A R : Type} [DecidableEq A] (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (rows : R→V→Bool) (pos : ∃ r,predicate (rows r))
    (boundary : ∀ r,BoundaryRow ((run 14 gs).wires.getD out default) (rows r))
    (port : Support 14→Option A) (signal : R→A→Prop)
    (agree : ∀ r s,Regular (survivors ((run 14 gs).wires.getD out default)) s →
      ((port s).elim False (signal r) ↔ lit s (rows r))) :
    let w := (run 14 gs).wires.getD out default
    ∃ book : List (Binary.Tree A), ∃ t : Binary.Tree A, Binary.Built book ∧ Binary.Ready book t ∧
      (∀ r,t.eval (signal r) ↔ predicate (rows r)) ∧
      (survivors w).card+w.jobs.card+book.length≤gs.length := by
  classical
  let w := (run 14 gs).wires.getD out default
  let H := survivors w
  obtain ⟨book,e,ok,ready,faith,count⟩ := circuitBook H w.jobs gs out
  have valid := (Checkpoint122.Pruning.port (run_valid 14 gs).1 out)
  have sound (z) (hz : accepts w z) := (spec z).mp (valid.sound z hz)
  let f : Label→Option A := Sum.elim port (fun _ => none)
  let dead := e.vars.filter (fun l => f l=none)
  have roots : w.jobs.image (Sum.inr : Product 14→Label)⊆dead := by
    rintro _ hl
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hl
    exact mem_filter.mpr ⟨faith.roots j hj hj,rfl⟩
  have dc := card_le_card roots
  rw [card_image_of_injective _ Sum.inr_injective] at dc
  have outer : H.card+book.length≤gs.length := by rw [count]; exact spentBound gs out spec
  have truth (r) : Zero.value (signal r) (Zero.reduce f e) ↔ predicate (rows r) := by
    have atLeaf (l : Label) (hl : l∈e.vars) : (f l).elim False (signal r) ↔ interpret (rows r) l := by
      cases l with
      | inl s => exact agree r s (faith.regular s hl)
      | inr j => rfl
    exact (Zero.semantics f _ e).trans ((Iff.intro (e.mono (fun l h => (atLeaf l h).mp))
      (e.mono (fun l h => (atLeaf l h).mpr))).trans
      ((faith.exactOn _ (boundaryDomain sound (boundary r))).trans (spec (rows r))))
  cases eq : Zero.reduce f e with
  | none =>
    obtain ⟨r,yes⟩ := pos
    have no := (truth r).mpr yes
    simp [eq,Zero.value] at no
  | some t =>
    obtain ⟨built,reached⟩ := Zero.library f ok
    have pay := Zero.cost f ok ready eq
    change (book.filterMap (Zero.emit f)).length+dead.card≤book.length at pay
    refine ⟨_,t,built,reached e ready t eq,fun r => by simpa [eq,Zero.value] using truth r,?_⟩
    change H.card+w.jobs.card+_≤gs.length
    omega

#print axioms boundaryDomain
#print axioms boundaryCircuit
end Checkpoint128.Heawood
