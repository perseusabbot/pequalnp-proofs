import AuxiliaryPath
import ZeroPruning

namespace Checkpoint126.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

private theorem tokenInj : Function.Injective token := by intro a b h; simpa [token] using h

private noncomputable def project (C : Finset V) (t : Label) : Option V := by
  classical
  exact if h : ∃ v∈C,t=token v then some h.choose else none

private theorem onToken (C : Finset V) (v : V) :
    project C (token v)=if v∈C then some v else none := by
  classical
  unfold project
  split_ifs with h hv hv
  · exact congrArg some (tokenInj h.choose_spec.2).symm
  · exact False.elim (hv (tokenInj h.choose_spec.2 ▸ h.choose_spec.1))
  · exact False.elim (h ⟨v,hv,rfl⟩)
  · rfl

private theorem projectionNone (C : Finset V) (t : Label) : project C t=none ↔ t∉C.image token := by
  classical
  by_cases h : ∃ v∈C,t=token v
  · obtain ⟨v,hv,rfl⟩ := h
    simp [onToken,hv,mem_image_of_mem token hv]
  · have away : t∉C.image token := fun m => h (by obtain ⟨v,hv,eq⟩ := mem_image.mp m; exact ⟨_,hv,eq.symm⟩)
    simp [project,h,away]

/-- Restrict to the missing cycle. Every other forced input has value zero.
Removing those inputs leaves a shared circuit for the cycle predicate. -/
private theorem noAux {q} (hq : q∈cores) {w : Wire 14} (sub : (Certificate.interior q.1).toFinset⊆lost w)
    (spec : ∀ z, w.full z=true ↔ predicate z) (sound : ∀ z, accepts w z → predicate z)
    {book : List Expr} {e : Expr} (built : Binary.Built book) (ready : Binary.Ready book e)
    (faith : Faithful (survivors w) w.jobs w e) (leaves : e.vars=forced w) :
    (forced w).card+1≤book.length := by
  classical
  let C := vertices q.1
  let f := project C
  let stem := C.image token
  have inc : stem⊆forced w := by
    rintro _ hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    exact mem_union_left _ (mem_image_of_mem _ (endpointsSub hq sub hv))
  have stemSz : stem.card=C.card := card_image_of_injective _ tokenInj
  have zeroSet : (e.vars.filter fun t => f t=none)=forced w \ stem := by
    ext t
    simp only [leaves,mem_filter,mem_sdiff,projectionNone,stem,f]
  have nb := atLeastTwo hq
  change 2≤C.card at nb
  have restriction (a : V→Bool) : Zero.value (fun v => a v=true) (Zero.reduce f e) ↔ predicate (clip q.1 a) := by
    let z := clip q.1 a
    have dom : Domain w.jobs z := domain sound sub (fun v hv => by by_contra neg; simp [z,clip,neg] at hv)
    have same (t : Label) (ht : t∈e.vars) : (f t).elim False (fun v => a v=true) ↔ interpret z t := by
      rw [leaves] at ht
      rcases mem_union.mp ht with lit|prod
      · obtain ⟨v,_,rfl⟩ := mem_image.mp lit
        change (project C (token v)).elim False (fun u => a u=true) ↔ Checkpoint122.Pruning.lit {v} z
        rw [onToken]
        by_cases on : v∈C <;> simp_all [Checkpoint122.Pruning.lit,z,clip,C]
      · obtain ⟨p,_,rfl⟩ := mem_image.mp prod
        have off : project C (.inr p)=none := (projectionNone ..).mpr (by simp [token])
        simp [f,off,interpret]
    exact (Zero.semantics f _ e).trans ((Iff.intro (e.mono (fun t ht => (same t ht).mp))
      (e.mono (fun t ht => (same t ht).mpr))).trans ((faith.exactOn _ dom).trans (spec z)))
  cases eq : Zero.reduce f e with
  | none =>
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0<C.card by omega)
    obtain ⟨a,_,yes,_,_,_⟩ := robust hq v hv v false
    have bad := (restriction a).mpr yes
    simp [eq,Zero.value] at bad
  | some t =>
    obtain ⟨newBuilt,reach⟩ := Zero.library f built
    have cap := Zero.cost f built ready eq
    have floor := Cherry.lower nb (robust hq) newBuilt (reach e ready t eq) (fun a => by
      simpa [eq,Zero.value] using restriction a)
    have sc := card_le_card inc
    rw [zeroSet,card_sdiff_of_subset inc,stemSz] at cap
    omega

/-- Losing an entire induced six- or eight-cycle costs two gates beyond the
unrestricted count of distinct terminal inputs minus one. -/
theorem cycleBudget (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (core : HasCore (lost ((run 14 gs).wires.getD out default))) :
    let w := (run 14 gs).wires.getD out default
    (survivors w).card+(endpoints (lost w)).card+w.jobs.card+1≤gs.length := by
  classical
  let s := run 14 gs
  let w := s.wires.getD out default
  obtain ⟨q,hq,sub⟩ := core
  obtain ⟨book,e,built,ready,faith,count⟩ := circuitBook (survivors w) w.jobs gs out
  have valid := (run_valid 14 gs).1
  have fw := port valid out
  have sound (z) (hz : accepts w z) := (spec z).mp (fw.sound z hz)
  have hs : survivors w⊆G.edgeFinset := (budget valid out spec).sub
  have inc : forced w⊆e.vars := required spec sound hs faith
  have cap : (survivors w).card+book.length≤gs.length := by
    rw [count]
    exact spentBound gs out spec
  have size := forcedSize w
  change (survivors w).card+(endpoints (lost w)).card+w.jobs.card+1≤gs.length
  by_contra! small
  have len : book.length≤(forced w).card := by omega
  obtain ⟨bound,saturated⟩ := Binary.inputBudget built ready
  by_cases same : e.vars=forced w
  · have grow : (forced w).card+1≤book.length := noAux hq sub spec sound built ready faith same
    omega
  · have proper := lt_of_le_of_ne (card_le_card inc) (fun eq => same (eq_of_subset_of_card_le inc eq.ge).symm)
    have gap := card_sdiff_of_subset inc
    have pos : (e.vars \ forced w).Nonempty := card_pos.mp (by omega)
    obtain ⟨extra,he⟩ := pos
    have one : (e.vars \ forced w).card≤1 := by omega
    have inside : e.vars⊆insert extra (forced w) := by
      intro t ht
      by_cases yes : t∈forced w
      · exact mem_insert_of_mem yes
      · exact mem_insert.mpr (Or.inl (card_le_one.mp one _ (mem_sdiff.mpr ⟨ht,yes⟩) _ he))
    exact auxiliaryPath hq sub spec sound hs faith extra (mem_sdiff.mp he).1 inside (saturated (by omega))

#print axioms cycleBudget
end Checkpoint126.Heawood
