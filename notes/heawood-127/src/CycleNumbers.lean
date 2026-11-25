import CycleAudit
import CoreGeometry

namespace Checkpoint126.Certificate
open Finset Checkpoint125.Certificate Checkpoint126.Heawood

private theorem disjointCore {es xs : List (Fin 21)} (ok : persists (coresIn es) xs=true) :
    ∃ q∈cores, ∀ i∈interior q.1, i∈es ∧ i∉xs := by
  obtain ⟨q,hq,passes⟩ := List.any_eq_true.mp ok
  obtain ⟨listed,insideAll⟩ := List.mem_filter.mp hq
  have subset : q.2 &&& word es=q.2 := eq_of_beq insideAll
  have apart : q.2 &&& word xs=0 := eq_of_beq passes
  refine ⟨q,listed,?_⟩
  intro i hi
  have bit : q.2.testBit i.val=true := by
    have eq := eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp bitsCorrect _ listed) i (List.mem_finRange _))
    exact eq ▸ (List.mem_filter.mp hi).2
  have a := congrArg (fun n : ℕ => n.testBit i.val) subset
  have b := congrArg (fun n : ℕ => n.testBit i.val) apart
  simp only [Nat.testBit_and,bit,Bool.true_and,Nat.zero_testBit] at a b
  exact ⟨(wordBit es i).mp a,fun mem => Bool.noConfusion (b.symm.trans ((wordBit xs i).mpr mem))⟩

theorem fromOmissions {es : List (Fin 21)} {L : Finset (Fin 21)} (nd : es.Nodup)
    (sub : L⊆es.toFinset)
    (allDrops : (es.sublistsLen (es.length-L.card)).all (persists (coresIn es))=true) : HasCore L := by
  let xs := es.filter (fun i => decide (i∉L))
  have eq : xs.toFinset=es.toFinset \ L := by ext i; simp [xs]
  have nodup : xs.Nodup := nd.filter _
  have len : xs.length=es.length-L.card := by
    rw [←List.toFinset_card_of_nodup nodup,eq,card_sdiff_of_subset sub,List.toFinset_card_of_nodup nd]
  have member : xs∈es.sublistsLen (es.length-L.card) := List.mem_sublistsLen.mpr ⟨List.filter_sublist,len⟩
  obtain ⟨q,hq,good⟩ := disjointCore (List.all_eq_true.mp allDrops xs member)
  refine ⟨q,hq,?_⟩
  intro i hi
  obtain ⟨mem,keep⟩ := good i (List.mem_toFinset.mp hi)
  by_contra gone
  exact keep (List.mem_filter.mpr ⟨mem,decide_eq_true gone⟩)

/-- The finite arithmetic check either supplies the gate bound immediately or
certifies a cycle inside the actual set of lost edges. -/
theorem numerical {d : ℕ} (db : d<16384) (L : Finset (Fin 21)) (sub : L⊆(interior d).toFinset)
    (ends : (vertexList d).length≤2*L.card) :
    let m := L.card
    let v := (vertexList d).length
    let base := 21-m+max ((21-m+2)/3) (retained d).length+v
    floorAt m+1≤base+(if 3*v<4*m then 1 else 0) ∨ (floorAt m+1≤base+2 ∧ HasCore L) := by
  let es := interior d
  have room : L.card≤es.length := (card_le_card sub).trans (List.toFinset_card_le _)
  have h := List.all_eq_true.mp (checked (d/128) (by omega)) (d%128) (List.mem_range.mpr (by omega))
  change checkSet (128*(d/128)+d%128)=true at h
  rw [show 128*(d/128)+d%128=d by omega] at h
  have row := List.all_eq_true.mp h L.card (List.mem_range.mpr (by change _ < es.length+1; omega))
  rcases Bool.or_eq_true_iff.mp row with first|cycle
  · rcases Bool.or_eq_true_iff.mp first with bad|ok
    · exact False.elim ((Nat.not_lt_of_ge ends) (of_decide_eq_true bad))
    · exact Or.inl (of_decide_eq_true ok)
  · obtain ⟨arith,allDrops⟩ := Bool.and_eq_true_iff.mp cycle
    refine Or.inr ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp arith).1,?_⟩
    exact fromOmissions ((List.nodup_finRange _).filter _) sub allDrops

#print axioms numerical
end Checkpoint126.Certificate
