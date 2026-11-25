import ThetaGeometry
import ThetaPorts

namespace Checkpoint128.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open Checkpoint125.Certificate Checkpoint126 Checkpoint127.Heawood Checkpoint128.Theta
open PEqualNP.Outside.L_meta_3004_aux.Controls

private def project (p : Shape) : Label→Option Slot
  | .inl s => if h : wordOf p s∈masks then some ⟨pack (wordOf p s),packMem h⟩ else none
  | .inr _ => none

/-- Restricting to any of the 84 embedded theta graphs produces an ordinary
binary circuit on its twelve allowed signals and pays for the missing labels. -/
theorem transfer (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    {p : Shape} (hp : p∈shapes)
    (sub : (interior p.domain).toFinset⊆lost ((run 14 gs).wires.getD out default)) :
    let w := (run 14 gs).wires.getD out default
    ∃ book : List (Binary.Tree Slot), ∃ t : Binary.Tree Slot, Binary.Built book ∧ Binary.Ready book t ∧
      Correct Subtype.val t ∧
      (survivors w).card+(endpoints (lost w)).card+w.jobs.card+book.length≤gs.length+9 := by
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
  let dead := e.vars.filter (fun l => f l=none)
  let C := Checkpoint126.Heawood.vertices p.domain
  have noZero : 0∉masks := by decide +kernel
  have lostInputs : forced w⊆dead∪C.image token := by
    intro l hl
    rcases mem_union.mp hl with atom|product
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp atom
      by_cases here : v∈C
      · exact mem_union_right _ (mem_image_of_mem token here)
      · have off := (countInfo hp).2 v here
        exact mem_union_left _ (mem_filter.mpr ⟨forcedLeaves hl,by simp [f,project,off,noZero]⟩)
    · obtain ⟨u,_,rfl⟩ := mem_image.mp product
      exact mem_union_left _ (mem_filter.mpr ⟨forcedLeaves hl,rfl⟩)
  have cost := (card_le_card lostInputs).trans (card_union_le ..)
  have inj : Function.Injective token := by intro a b eq; simpa [token] using eq
  rw [card_image_of_injective _ inj,forcedSize] at cost
  have cv : C.card=9 := (countInfo hp).1
  have cap : H.card+book.length≤gs.length := by rw [count]; exact spentBound gs out spec
  have atRow (row n : ℕ) (columns : ∀ m∈masks,(pack m).testBit n=(m &&& row != 0)) :
      Zero.value (fun v : Slot => v.val.testBit n=true) (Zero.reduce f e) ↔ predicate (sample p row) := by
    let z := sample p row
    have dom := Checkpoint126.Heawood.domain sound sub (fun v hv => inside hp row (v:=v) hv)
    have agree (l : Label) (hl : l∈e.vars) :
        (f l).elim False (fun v => v.val.testBit n=true) ↔ interpret z l := by
      cases l with
      | inr u => rfl
      | inl s =>
        have eligible := labelWord hp sub hs (faith.regular s hl)
        by_cases ok : wordOf p s∈masks
        · simpa only [f,project,dite_eq_left ok,Option.elim_some,columns _ ok,z,interpret] using wordOn p s row
        · have zero := (List.mem_cons.mp eligible).resolve_right ok
          have off : ¬lit s z := by rw [←wordOn,zero]; simp
          simp [f,project,ok,interpret,off]
    exact (Zero.semantics f _ e).trans ((Iff.intro (e.mono (fun l hl => (agree l hl).mp))
      (e.mono (fun l hl => (agree l hl).mpr))).trans ((faith.exactOn _ dom).trans (spec z)))
  have main (i : Fin width) :
      Zero.value (fun v : Slot => v.val.testBit i.val=true) (Zero.reduce f e) ∧
      ¬Zero.value (fun v : Slot => v.val.testBit (width+i.val)=true) (Zero.reduce f e) := by
    obtain ⟨pos,neg⟩ := sampleRows i
    exact ⟨(atRow _ _ (fun m hm => (packBits hm i).1)).mpr (samplePos hp pos),
      fun yes => sampleNeg hp neg ((atRow _ _ (fun m hm => (packBits hm i).2)).mp yes)⟩
  cases eq : Zero.reduce f e with
  | none =>
    have impossible := (main ⟨0,by decide⟩).1
    simp [eq,Zero.value] at impossible
  | some t =>
    obtain ⟨ok,reach⟩ := Zero.library f built
    have spend := Zero.cost f built ready eq
    change (book.filterMap (Zero.emit f)).length+dead.card≤book.length at spend
    refine ⟨_,t,ok,reach e ready t eq,fun i => by simpa [eq,Zero.value] using main i,?_⟩
    change H.card+(endpoints (lost w)).card+w.jobs.card+_≤gs.length+9
    omega

#print axioms transfer
end Checkpoint128.Heawood
