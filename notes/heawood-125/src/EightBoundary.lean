import LossFloor

namespace Checkpoint125.Heawood
open Finset Checkpoint122.Pruning Checkpoint125.Certificate
open PEqualNP.Outside.L_meta_3004_aux.Controls

private def smallCheck (d : ℕ) :=
  decide ((vertexList d).length<8 → (interior d).length<8)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem smallBlocks (b : ℕ) (bound : b<128) :
    (List.range 128).all (fun i => smallCheck (128*b+i))=true := by
  interval_cases b <;> decide +kernel

private theorem eightVertices (d : ℕ) (bound : d<16384) (room : 8≤(interior d).length) :
    8≤(vertexList d).length := by
  have h := List.all_eq_true.mp (smallBlocks (d/128) (by omega)) (d%128) (List.mem_range.mpr (by omega))
  change smallCheck (128*(d/128)+d%128)=true at h
  rw [show 128*(d/128)+d%128=d by omega] at h
  have cap := of_decide_eq_true h
  omega

/-- Exactly eight losses at the posted limit force 26 gates, eight endpoints
and five surviving ordinary products. The lost graph contains a three-edge path. -/
theorem eightProfile (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) (eight : missed ((run 14 gs).wires.getD out default)=8) :
    let w := (run 14 gs).wires.getD out default
    gs.length=26 ∧ (endpoints (lost w)).card=8 ∧ w.jobs.card=5 ∧ ContainsPath (lost w) := by
  let w := (run 14 gs).wires.getD out default
  let v := (endpoints (lost w)).card
  let j := w.jobs.card
  have valid := (run_valid 14 gs).1
  have fw := port valid out
  have b := budget valid out spec
  have sub : survivors w⊆G.edgeFinset := b.sub
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have loss : (lost w).card=8 := (lostSize w).trans eight
  have count : (survivors w).card=13 := by
    change missed w=8 at eight
    rw [missed,card_sdiff_of_subset sub,tally] at eight
    omega
  have star : (survivors w).card≤3*j := b.cubic
  have base : (survivors w).card+v+j≤gs.length+1 := (terminalBudget gs out spec).1
  obtain ⟨d,db,dv,cap,_,_⟩ := maskWitness (w:=w) (fun z hz => (spec z).mp (fw.sound z hz))
  change (vertexList d).length=v at dv
  rw [loss] at cap
  have vs := eightVertices d db cap
  have dense : 3*v<4*(lost w).card := by omega
  have path := densePath (lost w) dense
  have cost : (survivors w).card+v+j≤gs.length := pathBudget gs out spec path
  change gs.length=26 ∧ v=8 ∧ j=5 ∧ ContainsPath (lost w)
  exact ⟨by omega,by omega,by omega,path⟩

#print axioms eightProfile
end Checkpoint125.Heawood
