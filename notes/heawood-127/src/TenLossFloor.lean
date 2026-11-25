import FloorAudit
import OrbitProof
import SmallControls

namespace Checkpoint127.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

theorem gateFloor (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    Numbers.floorAt (missed ((run 14 gs).wires.getD out default))≤gs.length :=
  (Numbers.bounds Numbers.checked gs out spec).1

private theorem cutoffs : ∀ m : Fin 22,
    (Numbers.floorAt m≤26 → 10 ≤ m.val) ∧ (Numbers.floorAt m≤25 → 12 ≤ m.val) ∧
    (Numbers.floorAt m≤24 → 12 ≤ m.val) ∧ (Numbers.floorAt m≤23 → 14 ≤ m.val) ∧
    (Numbers.floorAt m≤22 → 15 ≤ m.val) ∧ (Numbers.floorAt m≤21 → 16 ≤ m.val) := by decide +kernel

theorem shortCircuits (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    let m := missed ((run 14 gs).wires.getD out default)
    (gs.length≤26 → 10 ≤ m) ∧ (gs.length≤25 → 12 ≤ m) ∧ (gs.length≤24 → 12 ≤ m) ∧
    (gs.length≤23 → 14 ≤ m) ∧ (gs.length≤22 → 15 ≤ m) ∧ (gs.length≤21 → 16 ≤ m) := by
  let w := (run 14 gs).wires.getD out default
  have bound : missed w≤21 := by rw [←lostSize]; exact_mod_cast (Finset.card_le_univ (lost w))
  have low : Numbers.floorAt (missed w)≤gs.length := gateFloor gs out spec
  obtain ⟨a,b,c,d,e,f⟩ := cutoffs ⟨missed w,by omega⟩
  exact ⟨fun n => a (low.trans n),fun n => b (low.trans n),fun n => c (low.trans n),
    fun n => d (low.trans n),fun n => e (low.trans n),fun n => f (low.trans n)⟩

/-- At exactly ten losses a short circuit must have 26 gates, eleven
surviving edges, nine lost endpoints and four retained products. -/
theorem tenProfile (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) (ten : missed ((run 14 gs).wires.getD out default)=10) :
    let w := (run 14 gs).wires.getD out default
    gs.length=26 ∧ (survivors w).card=11 ∧ (endpoints (lost w)).card=9 ∧ w.jobs.card=4 ∧
    Numbers.edgeMaskOf (lost w)∈Ten.masks := by
  let w := (run 14 gs).wires.getD out default
  have chosen := (Numbers.bounds Numbers.checked gs out spec).2 ten short
  change Numbers.edgeMaskOf (lost w)∈Ten.masks at chosen
  obtain ⟨nine,p,hp,cyc,inside⟩ := tenGeometry chosen
  have pay := patchBudget gs out spec p hp inside
  change (survivors w).card+(endpoints (lost w)).card+w.jobs.card+8≤gs.length+(if p.claw then 7 else 6) at pay
  simp only [cyc,Bool.false_eq_true,ite_false] at pay
  have valid := (run_valid 14 gs).1
  have bounds := budget valid out spec
  have sub : survivors w⊆G.edgeFinset := bounds.sub
  have star : (survivors w).card≤3*w.jobs.card := bounds.cubic
  have count : (survivors w).card=11 := by
    have tally : G.edgeFinset.card=21 := by decide +kernel
    change missed w=10 at ten
    rw [missed,card_sdiff_of_subset sub,tally] at ten
    have := card_le_card sub
    omega
  change gs.length=26 ∧ (survivors w).card=11 ∧ (endpoints (lost w)).card=9 ∧ w.jobs.card=4 ∧ _
  exact ⟨by omega,count,nine,by omega,chosen⟩

/-- The exact 65-opening search requires at least ten missing edge inputs. -/
theorem postedTenLost (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (wit : Checkpoint122.Posted.Witness i f g tail) :
    let qs := Checkpoint122.Posted.codes i f g tail
    10 ≤ missed ((run 14 (qs.map Checkpoint122.Posted.decode)).wires.getD (13+qs.length) default) := by
  apply (shortCircuits _ _ (Checkpoint122.Posted.semantics _ wit.2)).1
  have bound := wit.1
  simp only [List.length_map,Checkpoint122.Posted.codes,List.length_cons]
  omega

#print axioms gateFloor
#print axioms shortCircuits
#print axioms tenProfile
#print axioms postedTenLost
end Checkpoint127.Heawood
