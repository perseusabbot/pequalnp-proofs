import NineProfile
import EightPatterns

namespace Checkpoint126.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

private def allowed (cs : List V) :=
  let es := outside cs
  (es.length != 9) || Nine.masks.contains (edgeWord es.toFinset) ||
    (decide (10≤(endpoints es.toFinset).card) && Certificate.persists (Certificate.coresIn es) [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem centersChecked : ((List.finRange 14).sublistsLen 4).all allowed=true := by decide +kernel

/-- Every possible nine-loss mask occurs on this explicit list. -/
theorem ninePatterns (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) (nine : missed ((run 14 gs).wires.getD out default)=9) :
    edgeWord (lost ((run 14 gs).wires.getD out default))∈Nine.masks := by
  classical
  let w := (run 14 gs).wires.getD out default
  obtain ⟨_,four,twelve,profiles⟩ := nineProfile gs out spec short nine
  change w.jobs.card=4 at four
  change (survivors w).card=12 at twelve
  change ((endpoints (lost w)).card=9 ∧ HasCore (lost w) ∨ (endpoints (lost w)).card=10 ∧ ¬HasCore (lost w)) at profiles
  have fw := port (run_valid 14 gs).1 out
  obtain ⟨C,size,fit⟩ := Checkpoint123.Heawood.centers (w:=w) (fun z hz => (spec z).mp (fw.sound z hz))
  have degree : ∀ v, (star v).card=3 := by decide +kernel
  have cap : (incident C).card≤3*C.card := calc
    _ ≤ ∑ v∈C,(star v).card := card_biUnion_le
    _ = 3*C.card := by simp [degree,Nat.mul_comm]
  have room := card_le_card fit
  have cc : C.card=4 := by omega
  let cs := (List.finRange 14).filter (fun v => decide (v∈C))
  have eq : cs.toFinset=C := by ext v; simp [cs]
  have nd : cs.Nodup := (List.nodup_finRange _).filter _
  have len : cs.length=4 := by rw [←List.toFinset_card_of_nodup nd,eq,cc]
  have member : cs∈(List.finRange 14).sublistsLen 4 := List.mem_sublistsLen.mpr ⟨List.filter_sublist,len⟩
  have cover : survivors w=incident cs.toFinset := by rw [eq]; exact eq_of_subset_of_card_le fit (by omega)
  have inj : Function.Injective edge := by change ∀ i j : Fin 21,edge i=edge j → i=j; decide +kernel
  have same : (outside cs).toFinset=lost w := Finset.image_injective inj (by rw [outsideEdges,←cover,lostEdges])
  have listed := List.all_eq_true.mp centersChecked cs member
  let es := outside cs
  have dn : es.Nodup := (List.nodup_finRange _).filter _
  have nineEdges : es.length=9 := by rw [←List.toFinset_card_of_nodup dn]; exact same ▸ (lostSize w).trans nine
  rcases Bool.or_eq_true_iff.mp listed with simple|bad
  · rcases Bool.or_eq_true_iff.mp simple with wrong|ok
    · change (es.length != 9)=true at wrong
      simp [nineEdges] at wrong
    · change edgeWord (lost w)∈Nine.masks
      rw [←same]
      exact List.contains_iff_mem.mp ok
  · obtain ⟨many,found⟩ := Bool.and_eq_true_iff.mp bad
    have v10 : 10≤(endpoints (lost w)).card := same ▸ of_decide_eq_true many
    have has : HasCore (lost w) := Certificate.fromOmissions dn same.symm.subset (by
      have count : es.length=(lost w).card := (List.toFinset_card_of_nodup dn).symm.trans (congrArg Finset.card same)
      simp only [count,Nat.sub_self,List.sublistsLen_zero,List.all_cons,List.all_nil,Bool.and_true]
      exact found)
    rcases profiles with ⟨small,_⟩|⟨_,no⟩
    · omega
    · exact False.elim (no has)

set_option maxRecDepth 10000 in
theorem nineCount : Nine.masks.length=126 ∧ Nine.masks.IsChain (· < ·) := by decide +kernel

#print axioms ninePatterns
#print axioms nineCount
end Checkpoint126.Heawood
