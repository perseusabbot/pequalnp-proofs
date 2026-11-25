import CycleNumbers
import CycleBudget
import LossFloor

namespace Checkpoint126.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood Checkpoint125.Certificate
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Gate floors in all 22 exact loss classes of the Heawood edge function. -/
theorem gateFloor (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    Certificate.floorAt (missed ((run 14 gs).wires.getD out default)) ≤ gs.length := by
  let w := (run 14 gs).wires.getD out default
  let m := (lost w).card
  let v := (endpoints (lost w)).card
  let h := (survivors w).card
  let j := w.jobs.card
  have valid := (run_valid 14 gs).1
  have fw := port valid out
  have bounds := budget valid out spec
  have sub : survivors w⊆G.edgeFinset := bounds.sub
  have cubicBound : h ≤ 3*j := bounds.cubic
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have split : m+h=21 := by
    have le := card_le_card sub
    change (lost w).card+(survivors w).card=21
    rw [lostSize,missed,card_sdiff_of_subset sub,tally]
    omega
  obtain ⟨d,db,dv,inner,two,packing⟩ := maskWitnessSub (w:=w) (fun z hz => (spec z).mp (fw.sound z hz))
  change (vertexList d).length=v at dv
  change v ≤ 2*m at two
  change (retained d).length ≤ j at packing
  have num := Certificate.numerical db (lost w) inner (dv ▸ two)
  change Certificate.floorAt m+1 ≤ 21-m+max ((21-m+2)/3) (retained d).length+(vertexList d).length+
    (if 3*(vertexList d).length<4*m then 1 else 0) ∨
    (Certificate.floorAt m+1 ≤ 21-m+max ((21-m+2)/3) (retained d).length+(vertexList d).length+2 ∧ HasCore (lost w)) at num
  rw [dv] at num
  have cover : max ((21-m+2)/3) (retained d).length ≤ j := max_le (by omega) packing
  change Certificate.floorAt (missed w) ≤ gs.length
  rw [←lostSize]
  change Certificate.floorAt m ≤ gs.length
  rcases num with old|⟨step,core⟩
  · split_ifs at old with dense
    · have path := densePath (lost w) dense
      have strict : h+v+j ≤ gs.length := pathBudget gs out spec path
      omega
    · have base : h+v+j ≤ gs.length+1 := (terminalBudget gs out spec).1
      omega
  · have strict : h+v+j+1 ≤ gs.length := cycleBudget gs out spec core
    omega

private theorem cutoffs : ∀ m : Fin 22,
    (Certificate.floorAt m ≤ 26 → 9 ≤ m.val) ∧ (Certificate.floorAt m ≤ 25 → 10 ≤ m.val) ∧
    (Certificate.floorAt m ≤ 24 → 12 ≤ m.val) ∧ (Certificate.floorAt m ≤ 23 → 12 ≤ m.val) ∧
    (Certificate.floorAt m ≤ 22 → 14 ≤ m.val) ∧ (Certificate.floorAt m ≤ 21 → 15 ≤ m.val) := by decide +kernel

theorem shortCircuits (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    let m := missed ((run 14 gs).wires.getD out default)
    (gs.length ≤ 26 → 9 ≤ m) ∧ (gs.length ≤ 25 → 10 ≤ m) ∧ (gs.length ≤ 24 → 12 ≤ m) ∧
    (gs.length ≤ 23 → 12 ≤ m) ∧ (gs.length ≤ 22 → 14 ≤ m) ∧ (gs.length ≤ 21 → 15 ≤ m) := by
  let w := (run 14 gs).wires.getD out default
  have bound : missed w ≤ 21 := by rw [←lostSize]; exact_mod_cast (Finset.card_le_univ (lost w))
  have low : Certificate.floorAt (missed w) ≤ gs.length := gateFloor gs out spec
  obtain ⟨a,b,c,d,e,f⟩ := cutoffs ⟨missed w,by omega⟩
  exact ⟨fun n => a (low.trans n),fun n => b (low.trans n),fun n => c (low.trans n),
    fun n => d (low.trans n),fun n => e (low.trans n),fun n => f (low.trans n)⟩

/-- Every witness in the posted 65-opening search loses at least nine
individual edge inputs when nested AND outputs are forced to zero. -/
theorem postedNineLost (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (wit : Checkpoint122.Posted.Witness i f g tail) :
    let qs := Checkpoint122.Posted.codes i f g tail
    9 ≤ missed ((run 14 (qs.map Checkpoint122.Posted.decode)).wires.getD (13+qs.length) default) := by
  apply (shortCircuits _ _ (Checkpoint122.Posted.semantics _ wit.2)).1
  have bound := wit.1
  simp only [List.length_map,Checkpoint122.Posted.codes,List.length_cons]
  omega

#print axioms gateFloor
#print axioms shortCircuits
#print axioms postedNineLost
end Checkpoint126.Heawood
