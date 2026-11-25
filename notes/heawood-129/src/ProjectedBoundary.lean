import BoundaryRows

namespace Checkpoint129.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open Checkpoint125.Certificate Checkpoint126 Checkpoint128.Heawood PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Restrict to boundary assignments on a vertex set. Each forced singleton outside
the set and each retained product pays for a removed gate in the reduced library. -/
theorem projectedBoundaryCircuit {A R : Type} [DecidableEq A] (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (rows : R→V→Bool) (pos : ∃ r,predicate (rows r))
    (boundary : ∀ r,BoundaryRow ((run 14 gs).wires.getD out default) (rows r))
    (points : Finset V) (port : Support 14→Option A)
    (outside : ∀ v : V,v∉points → port {v}=none) (signal : R→A→Prop)
    (agree : ∀ r s,Regular (survivors ((run 14 gs).wires.getD out default)) s →
      ((port s).elim False (signal r) ↔ lit s (rows r))) :
    let w := (run 14 gs).wires.getD out default
    ∃ book : List (Binary.Tree A), ∃ t : Binary.Tree A, Binary.Built book ∧ Binary.Ready book t ∧
      (∀ r,t.eval (signal r) ↔ predicate (rows r)) ∧
      (survivors w).card+(endpoints (lost w)).card+w.jobs.card+book.length≤gs.length+points.card := by
  classical
  let w := (run 14 gs).wires.getD out default
  let H := survivors w
  obtain ⟨book,e,ok,ready,faith,count⟩ := circuitBook H w.jobs gs out
  have valid := (Checkpoint122.Pruning.port (run_valid 14 gs).1 out)
  have sound (z) (hz : accepts w z) := (spec z).mp (valid.sound z hz)
  let f : Label→Option A := Sum.elim port (fun _ => none)
  let dead := e.vars.filter (fun l => f l=none)
  have hs : H⊆G.edgeFinset := (budget (run_valid 14 gs).1 out spec).sub
  have leaves : forced w⊆e.vars := required spec sound hs faith
  have charged : forced w⊆dead∪points.image token := by
    intro l hl
    rcases mem_union.mp hl with atom|product
    · obtain ⟨v,_,rfl⟩ := mem_image.mp atom
      by_cases here : v∈points
      · exact mem_union_right _ (mem_image_of_mem token here)
      · exact mem_union_left _ (mem_filter.mpr ⟨leaves hl,outside v here⟩)
    · obtain ⟨j,_,rfl⟩ := mem_image.mp product
      exact mem_union_left _ (mem_filter.mpr ⟨leaves hl,rfl⟩)
  have dc := (card_le_card charged).trans (card_union_le ..)
  have inj : Function.Injective token := by intro a b eq; simpa [token] using eq
  rw [card_image_of_injective _ inj,forcedSize] at dc
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
    change H.card+(endpoints (lost w)).card+w.jobs.card+_≤gs.length+points.card
    omega

#print axioms projectedBoundaryCircuit
end Checkpoint129.Heawood
