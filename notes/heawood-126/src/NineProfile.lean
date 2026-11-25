import NineData
import NineLossFloor

namespace Checkpoint126.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood Checkpoint125.Certificate
open PEqualNP.Outside.L_meta_3004_aux.Controls

private def PackSix (es : List (Fin 21)) := es.length=6 ∧ es.Nodup ∧
  ∀ i∈es, ∀ j∈es,i≠j → Disjoint (ends i) (ends j)
private instance (es) : Decidable (PackSix es) := by unfold PackSix; infer_instance

private theorem packs : Nine.matchings.all (fun es => decide (PackSix es))=true := by decide +kernel

private def smallNine (d : ℕ) :=
  let v := (vertexList d).length
  let es := interior d
  decide (9<v ∨ es.length<9) ||
    (decide (8≤v) && (decide (8<v) || Nine.matchings.any (fun xs => xs.all (fun i => !inside d i))) &&
      (es.sublistsLen (es.length-9)).all (Certificate.persists (Certificate.coresIn es)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem smallBlocks (b : ℕ) (bound : b<128) :
    (List.range 128).all (fun i => smallNine (128*b+i))=true := by
  interval_cases b <;> decide +kernel

private theorem smallNineFacts {w : Wire 14} (sound : ∀ z, accepts w z → predicate z) {d : ℕ} (db : d<16384)
    (sub : lost w⊆(interior d).toFinset) (loss : (lost w).card=9) (small : (vertexList d).length≤9) :
    8≤(vertexList d).length ∧ HasCore (lost w) ∧ ((vertexList d).length≤8 → 6≤w.jobs.card) := by
  have room := (card_le_card sub).trans (List.toFinset_card_le _)
  have h := List.all_eq_true.mp (smallBlocks (d/128) (by omega)) (d%128) (List.mem_range.mpr (by omega))
  rw [show 128*(d/128)+d%128=d by omega] at h
  rcases Bool.or_eq_true_iff.mp h with skip|row
  · rcases of_decide_eq_true skip with big|few <;> omega
  obtain ⟨limits,cycles⟩ := Bool.and_eq_true_iff.mp row
  obtain ⟨eight,choice⟩ := Bool.and_eq_true_iff.mp limits
  refine ⟨of_decide_eq_true eight,Certificate.fromOmissions ((List.nodup_finRange _).filter _) sub (by rwa [loss]),?_⟩
  intro tiny
  rcases Bool.or_eq_true_iff.mp choice with big|somePack
  · have := of_decide_eq_true big
    omega
  obtain ⟨es,member,fit⟩ := List.any_eq_true.mp somePack
  obtain ⟨six,nd,apart⟩ := of_decide_eq_true (List.all_eq_true.mp packs es member)
  rw [←six]
  apply jobsOfMatching sound es nd apart
  intro i hi
  by_contra gone
  have away := List.all_eq_true.mp fit i hi
  have insideEdge : i∈interior d := List.mem_toFinset.mp (sub (mem_filter.mpr ⟨mem_univ _,gone⟩))
  simp [(List.mem_filter.mp insideEdge).2] at away

/-- At nine losses and 26 gates the twelve surviving edges need four
ordinary products. The missing edges touch nine or ten vertices. -/
theorem nineProfile (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) (nine : missed ((run 14 gs).wires.getD out default)=9) :
    let w := (run 14 gs).wires.getD out default
    gs.length=26 ∧ w.jobs.card=4 ∧ (survivors w).card=12 ∧
    ((endpoints (lost w)).card=9 ∧ HasCore (lost w) ∨ (endpoints (lost w)).card=10 ∧ ¬HasCore (lost w)) := by
  let w := (run 14 gs).wires.getD out default
  let v := (endpoints (lost w)).card
  let j := w.jobs.card
  have valid := (run_valid 14 gs).1
  have fw := port valid out
  have bounds := budget valid out spec
  have sub : survivors w⊆G.edgeFinset := bounds.sub
  have sound (z) (hz : accepts w z) := (spec z).mp (fw.sound z hz)
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have loss : (lost w).card=9 := (lostSize w).trans nine
  have count : (survivors w).card=12 := by
    change missed w=9 at nine
    rw [missed,card_sdiff_of_subset sub,tally] at nine
    have := card_le_card sub
    omega
  have star : (survivors w).card≤3*j := bounds.cubic
  have base : (survivors w).card+v+j≤gs.length+1 := (terminalBudget gs out spec).1
  have dense : 3*v<4*(lost w).card := by omega
  have path : (survivors w).card+v+j≤gs.length := pathBudget gs out spec (densePath (lost w) dense)
  have stronger (hc : HasCore (lost w)) : (survivors w).card+v+j+1≤gs.length := cycleBudget gs out spec hc
  change gs.length=26 ∧ j=4 ∧ (survivors w).card=12 ∧ (v=9 ∧ _ ∨ v=10 ∧ _)
  by_cases small : v≤9
  · obtain ⟨d,db,dv,inner,_,_⟩ := maskWitnessSub sound
    change (vertexList d).length=v at dv
    obtain ⟨eight,core,pack⟩ := smallNineFacts sound db inner loss (dv ▸ small)
    rw [dv] at eight pack
    change v≤8 → 6≤j at pack
    have cap := stronger core
    exact ⟨by omega,by omega,count,Or.inl ⟨by omega,core⟩⟩
  · exact ⟨by omega,by omega,count,Or.inr ⟨by omega,fun hc => by have := stronger hc; omega⟩⟩

#print axioms nineProfile
end Checkpoint126.Heawood
