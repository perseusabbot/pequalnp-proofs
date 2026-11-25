import ContractCircuit
import ForcedInputs

namespace Checkpoint125.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Contract
open PEqualNP.Outside.L_meta_3004_aux.Controls

def forced (w : Wire 14) : Finset Label :=
  (endpoints (lost w)).image (fun v => Sum.inl {v}) ∪ w.jobs.image Sum.inr

theorem forcedSize (w : Wire 14) : (forced w).card=(endpoints (lost w)).card+w.jobs.card := by
  have inj : Function.Injective (fun v : V => (Sum.inl {v} : Label)) := by intro x y h; simpa using h
  have disjoint : Disjoint ((endpoints (lost w)).image (fun v => (Sum.inl {v} : Label))) (w.jobs.image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro l hl hr
    obtain ⟨v,_,rfl⟩ := mem_image.mp hl
    simp at hr
  rw [forced,card_union_of_disjoint disjoint,card_image_of_injective _ inj,card_image_of_injective _ Sum.inr_injective]

theorem required {w : Wire 14} (spec : ∀ z, w.full z=true ↔ predicate z)
    (sound : ∀ z, accepts w z → predicate z) (sub : survivors w⊆G.edgeFinset)
    {e} (faith : Faithful (survivors w) w.jobs w e) : forced w⊆e.vars := by
  have domain {z} (no : ¬accepts w z) : Domain w.jobs z := fun p hp both => no (Or.inr ⟨p,hp,both⟩)
  have literal (i : Fin 21) (gone : edge i∉survivors w) (k : Bool) : Sum.inl {endpoint i k}∈e.vars := by
    have ph : Domain w.jobs (positive i) := domain (fun ha => gone ((survives_iff sound ..).mpr ha))
    have nh : Domain w.jobs (negative i k) := domain (fun ha => negativeNo i k (sound _ ha))
    have yes := (faith.exactOn _ ph).mpr ((spec _).mpr (positiveYes i))
    have no : ¬e.eval (interpret (negative i k)) := fun h => negativeNo i k ((spec _).mp ((faith.exactOn _ nh).mp h))
    by_contra missing
    apply no
    apply e.mono _ yes
    rintro (S|p) mem h
    · by_contra off
      exact missing ((onlyLiteral sub gone k (faith.regular _ mem) h off) ▸ mem)
    · exact False.elim h
  intro l hl
  rcases mem_union.mp hl with v|p
  · obtain ⟨u,hu,rfl⟩ := mem_image.mp v
    obtain ⟨i,hi,hu⟩ := mem_biUnion.mp hu
    rcases mem_insert.mp hu with rfl|hu
    · exact literal i (mem_filter.mp hi).2 false
    · obtain rfl := mem_singleton.mp hu
      exact literal i (mem_filter.mp hi).2 true
  · obtain ⟨item,hp,rfl⟩ := mem_image.mp p
    exact faith.roots item hp hp

theorem spentBound (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    let s := run 14 gs
    let w := s.wires.getD out default
    (survivors w).card+spent (survivors w) w.jobs s≤gs.length := by
  let s := run 14 gs
  let w := s.wires.getD out default
  obtain ⟨v,count⟩ := run_valid 14 gs
  have fw := port v out
  have sound (z) (h : accepts w z) := (spec z).mp (fw.sound z h)
  have b := chargedBottom s.bottom v.bottom (fun p hp => v.operands p (fw.owned p hp)) sound
  change (survivors w).card+waste (survivors w) s.bottom ≤ w.jobs.card+s.bottom.length at b
  have p := chargeProducts v out
  change w.jobs.card+extra w.jobs s ≤ s.products.length+s.bypass at p
  change s.bottom.length+s.top.length+s.products.length+s.dropped+s.bypass=gs.length at count
  change (survivors w).card+spent (survivors w) w.jobs s≤gs.length
  unfold spent
  omega

/-- Equality gives a read-once formula whose leaves are exactly the lost
endpoints' literals and the zero placeholders for retained products. -/
theorem terminalBudget (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    let s := run 14 gs
    let w := s.wires.getD out default
    let n := (survivors w).card+(endpoints (lost w)).card+w.jobs.card
    n ≤ gs.length+1 ∧ (n=gs.length+1 →
      ∃ e : Expr, Faithful (survivors w) w.jobs w e ∧ e.vars=forced w ∧ e.inputs.Nodup) := by
  let s := run 14 gs
  let w := s.wires.getD out default
  obtain ⟨v,count⟩ := run_valid 14 gs
  have fw := port v out
  have sound (z) (h : accepts w z) := (spec z).mp (fw.sound z h)
  have cap : (survivors w).card+spent (survivors w) w.jobs s≤gs.length := spentBound gs out spec
  obtain ⟨e,faith,bound,saturated⟩ := circuit (survivors w) w.jobs gs out
  change e.vars.card ≤ spent (survivors w) w.jobs s+1 at bound
  have inc : forced w⊆e.vars := required spec sound (budget v out spec).sub faith
  have lb := card_le_card inc
  rw [forcedSize] at lb
  change (survivors w).card+(endpoints (lost w)).card+w.jobs.card ≤ gs.length+1 ∧ _
  refine ⟨by omega,?_⟩
  intro tight
  change (survivors w).card+(endpoints (lost w)).card+w.jobs.card=gs.length+1 at tight
  have eq : forced w=e.vars := eq_of_subset_of_card_le inc (by rw [forcedSize]; omega)
  refine ⟨e,faith,eq.symm,saturated ?_⟩
  change e.vars.card=spent (survivors w) w.jobs s+1
  omega

#print axioms terminalBudget
end Checkpoint125.Heawood
