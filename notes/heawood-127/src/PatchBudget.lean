import PatchGeometry
import CycleBudget

namespace Checkpoint127.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open Checkpoint126 PEqualNP.Outside.L_meta_3004_aux.Controls

private def project (p : Patch) : Label→Option (Small.Slot p.claw)
  | .inl s => if h : maskOf p s∈Small.palette p.claw then some ⟨maskOf p s,h⟩ else none
  | .inr _ => none

private theorem noZero (k : Bool) : 0∉Small.palette k := by cases k <;> decide
private theorem tokenInj : Function.Injective token := by intro a b h; simpa [token] using h

/-- Restricting to the six-cycle or the seven-vertex subdivided claw leaves
at least eight gates after the other forced terminal labels are deleted. -/
theorem patchBudget (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (p : Patch) (hp : p∈patches)
    (sub : (Checkpoint125.Certificate.interior p.d).toFinset⊆lost ((run 14 gs).wires.getD out default)) :
    let w := (run 14 gs).wires.getD out default
    (survivors w).card+(endpoints (lost w)).card+w.jobs.card+8≤gs.length+(if p.claw then 7 else 6) := by
  classical
  let w := (run 14 gs).wires.getD out default
  let H := survivors w
  obtain ⟨book,e,built,ready,faith,count⟩ := circuitBook H w.jobs gs out
  have valid := (run_valid 14 gs).1
  have fw := port valid out
  have sound (z) (hz : accepts w z) := (spec z).mp (fw.sound z hz)
  have hs : H⊆G.edgeFinset := (budget valid out spec).sub
  have forcedLeaves : forced w⊆e.vars := required spec sound hs faith
  let f := project p
  let dead := e.vars.filter (fun t => f t=none)
  let C := Checkpoint126.Heawood.vertices p.d
  have lostInputs : forced w⊆dead∪C.image token := by
    intro t ht
    rcases mem_union.mp ht with sing|prod
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp sing
      by_cases inside : v∈C
      · exact mem_union_right _ (mem_image_of_mem token inside)
      · have off : maskOf p {v}=0 := emptyMask p (by
          intro u hu eq
          obtain rfl := mem_singleton.mp eq
          apply inside
          change u∈Checkpoint126.Heawood.vertices p.d
          rw [←orderSet hp]
          exact List.mem_toFinset.mpr hu)
        exact mem_union_left _ (mem_filter.mpr ⟨forcedLeaves ht,by simp [f,project,off,noZero]⟩)
    · obtain ⟨u,_,rfl⟩ := mem_image.mp prod
      exact mem_union_left _ (mem_filter.mpr ⟨forcedLeaves ht,rfl⟩)
  have lowerCount := (card_le_card lostInputs).trans (card_union_le ..)
  rw [card_image_of_injective _ tokenInj,forcedSize] at lowerCount
  have cv : C.card=(if p.claw then 7 else 6) := vertexCount hp
  have cap : H.card+book.length≤gs.length := by rw [count]; exact spentBound gs out spec
  have semantics (r : Small.Row) : Zero.value (fun v : Small.Slot p.claw => Small.signal v.val r=true)
      (Zero.reduce f e) ↔ Small.target p.claw r=true := by
    let z := sample p r
    have dom := Checkpoint126.Heawood.domain sound sub (fun v hv => supported hp r (v:=v) hv)
    have agree (t : Label) (ht : t∈e.vars) :
        (f t).elim False (fun v => Small.signal v.val r=true) ↔ interpret z t := by
      cases t with
      | inr item => rfl
      | inl s =>
        have ok := regularMask hp sub hs (faith.regular s ht)
        by_cases yes : maskOf p s∈Small.palette p.claw
        · simpa only [f,project,dite_eq_left yes,Option.elim_some,interpret,z] using maskTruth p s r
        · have no := ok.resolve_right yes
          have off : ¬lit s z := by rw [←maskTruth p s r,no]; simp [Small.signal]
          simp [f,project,yes,interpret,off]
    exact (Zero.semantics f _ e).trans ((Iff.intro (e.mono (fun t ht => (agree t ht).mp))
      (e.mono (fun t ht => (agree t ht).mpr))).trans ((faith.exactOn _ dom).trans ((spec z).trans (patchTruth hp r))))
  change H.card+(endpoints (lost w)).card+w.jobs.card+8≤gs.length+(if p.claw then 7 else 6)
  cases eq : Zero.reduce f e with
  | none =>
    have sat : ∀ k : Bool,Small.target k 127=true := by decide +kernel
    have bad := (semantics 127).mpr (sat _)
    simp [eq,Zero.value] at bad
  | some t =>
    obtain ⟨newBuilt,reach⟩ := Zero.library f built
    have spend := Zero.cost f built ready eq
    change (book.filterMap (Zero.emit f)).length+dead.card≤book.length at spend
    have floor := Small.lower newBuilt (reach e ready t eq) (fun r => by simpa [eq,Zero.value] using semantics r)
    omega

#print axioms patchBudget
end Checkpoint127.Heawood
