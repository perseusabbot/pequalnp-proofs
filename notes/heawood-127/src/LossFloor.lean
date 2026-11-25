import DensePaths
import VertexMasks
import MaskAudit
import PostedModel

namespace Checkpoint125.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Certificate
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Gate floors for each of the 22 possible counts of minimal positive inputs
lost when all AND gates with an AND-dependent input are forced to zero. -/
theorem gateFloor (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    floor (missed ((run 14 gs).wires.getD out default)) ≤ gs.length := by
  let w := (run 14 gs).wires.getD out default
  let m := (lost w).card
  let v := (endpoints (lost w)).card
  let h := (survivors w).card
  let j := w.jobs.card
  have valid := (run_valid 14 gs).1
  have fw := port valid out
  have bounds := budget valid out spec
  have sub : survivors w⊆G.edgeFinset := bounds.sub
  have cubicBound : h≤3*j := bounds.cubic
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have split : m+h=21 := by
    have le := card_le_card sub
    change (lost w).card+(survivors w).card=21
    rw [lostSize,missed,card_sdiff_of_subset sub,tally]
    omega
  obtain ⟨d,db,dv,inner,two,packing⟩ := maskWitness (w:=w) (fun z hz => (spec z).mp (fw.sound z hz))
  change (vertexList d).length=v at dv
  change m≤(interior d).length at inner
  change v≤2*m at two
  change (retained d).length≤j at packing
  have num := numerical db inner (dv ▸ two)
  rw [dv] at num
  have cover : max ((21-m+2)/3) (retained d).length ≤ j := max_le (by omega) packing
  have base : h+v+j≤gs.length+1 := (terminalBudget gs out spec).1
  have strong : h+v+j+(if 3*v<4*m then 1 else 0) ≤ gs.length+1 := by
    split_ifs with dense
    · have path := densePath (lost w) dense
      have strict : h+v+j≤gs.length := pathBudget gs out spec path
      omega
    · omega
  change floor (missed w)≤gs.length
  rw [←lostSize]
  change floor m≤gs.length
  omega

private theorem cutoffs : ∀ m : Fin 22,
    (floor m≤26 → 8≤ m.val) ∧ (floor m≤25 → 9≤ m.val) ∧ (floor m≤24 → 10≤ m.val) ∧
    (floor m≤23 → 12≤ m.val) ∧ (floor m≤22 → 12≤ m.val) ∧ (floor m≤21 → 14≤ m.val) := by decide +kernel

theorem shortCircuits (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    let m := missed ((run 14 gs).wires.getD out default)
    (gs.length≤26 → 8≤ m) ∧ (gs.length≤25 → 9≤ m) ∧ (gs.length≤24 → 10≤ m) ∧
    (gs.length≤23 → 12≤ m) ∧ (gs.length≤22 → 12≤ m) ∧ (gs.length≤21 → 14≤ m) := by
  let w := (run 14 gs).wires.getD out default
  have bound : missed w≤21 := by
    rw [←lostSize]
    exact_mod_cast (Finset.card_le_univ (lost w))
  have low : floor (missed w)≤gs.length := gateFloor gs out spec
  obtain ⟨a,b,c,d,e,f⟩ := cutoffs ⟨missed w,by omega⟩
  exact ⟨fun n => a (low.trans n),fun n => b (low.trans n),fun n => c (low.trans n),
    fun n => d (low.trans n),fun n => e (low.trans n),fun n => f (low.trans n)⟩

/-- Every witness to the posted 65-opening search must lose at least eight edges. -/
theorem postedEightLost (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (wit : Checkpoint122.Posted.Witness i f g tail) :
    let qs := Checkpoint122.Posted.codes i f g tail
    8 ≤ missed ((run 14 (qs.map Checkpoint122.Posted.decode)).wires.getD (13+qs.length) default) := by
  apply (shortCircuits _ _ (Checkpoint122.Posted.semantics _ wit.2)).1
  have bound := wit.1
  simp only [List.length_map,Checkpoint122.Posted.codes,List.length_cons]
  omega

#print axioms gateFloor
#print axioms shortCircuits
#print axioms postedEightLost
end Checkpoint125.Heawood
