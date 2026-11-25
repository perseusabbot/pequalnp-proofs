import PathObstruction

namespace Checkpoint125.Heawood
open Finset Checkpoint124.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def incidentTo (L : Finset (Fin 21)) (v : V) := L.filter fun i => v∈ends i
private theorem degreeCap : ∀ v, (incidentTo univ v).card=3 := by decide +kernel

/-- A middle edge with another lost edge at each endpoint extends to a
three-edge path. The graph has no triangles. -/
private theorem middle : ∀ i j k : Fin 21, j≠i → k≠i →
    endpoint i false∈ends j → endpoint i true∈ends k →
    ∃ p∈paths, p.links=[j,i,k] := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  decide +kernel

theorem densePath (L : Finset (Fin 21)) (dense : 3*(endpoints L).card < 4*L.card) : ContainsPath L := by
  classical
  by_contra absent
  let S := endpoints L
  let P := S.filter fun v => (incidentTo L v).card=1
  have endpointMem (i) (hi : i∈L) : ends i⊆S := fun _ hv => mem_biUnion.mpr ⟨i,hi,hv⟩
  have one (i) (hi : i∈L) : ∃ v∈P, i∈incidentTo L v := by
    have side (s : Bool) : endpoint i s∈ends i := by cases s <;> simp [ends]
    have each (s : Bool) : i∈incidentTo L (endpoint i s) := mem_filter.mpr ⟨hi,side s⟩
    have other (s : Bool) (bad : (incidentTo L (endpoint i s)).card≠1) :
        ∃ j∈L, j≠i ∧ endpoint i s∈ends j := by
      obtain ⟨j,hj⟩ : ((incidentTo L (endpoint i s)).erase i).Nonempty := by
        apply card_pos.mp
        rw [card_erase_of_mem (each s)]
        have pos := card_pos.mpr (show (incidentTo L (endpoint i s)).Nonempty from ⟨i,each s⟩)
        omega
      have h := mem_filter.mp (mem_of_mem_erase hj)
      exact ⟨j,h.1,ne_of_mem_erase hj,h.2⟩
    by_cases a : (incidentTo L (endpoint i false)).card=1
    · exact ⟨_,mem_filter.mpr ⟨endpointMem i hi (side false),a⟩,each false⟩
    by_cases b : (incidentTo L (endpoint i true)).card=1
    · exact ⟨_,mem_filter.mpr ⟨endpointMem i hi (side true),b⟩,each true⟩
    obtain ⟨j,hj,ji,jv⟩ := other false a
    obtain ⟨k,hk,ki,kv⟩ := other true b
    obtain ⟨p,hp,eq⟩ := middle i j k ji ki jv kv
    exact False.elim (absent ⟨p,hp,by simp [eq,hj,hi,hk]⟩)
  have pick (i : L) := one i.val i.property
  choose v vp mark using pick
  let f (i : L) : P := ⟨v i,vp i⟩
  have inject : Function.Injective f := by
    intro i j eq
    have same : v i=v j := congrArg Subtype.val eq
    have s1 := (mem_filter.mp (vp i)).2
    exact Subtype.ext (card_le_one.mp s1.le _ (mark i) _ (same ▸ mark j))
  have many := Fintype.card_le_of_injective f inject
  simp only [Fintype.card_coe] at many
  have degree (v : V) : (incidentTo L v).card ≤ 3 := (card_le_card
    (show incidentTo L v⊆incidentTo univ v from fun i h => mem_filter.mpr ⟨mem_univ i,(mem_filter.mp h).2⟩)).trans_eq (degreeCap v)
  have total : ∑ v∈S, (incidentTo L v).card=2*L.card := by
    simp only [incidentTo,card_filter]
    rw [sum_comm]
    calc
      _ = ∑ _∈L, 2 := sum_congr rfl (fun i hi => by
        rw [←card_filter]
        have eq : S.filter (fun v => v∈ends i)=ends i := by
          ext x
          exact mem_filter.trans (and_iff_right_of_imp (fun hx => endpointMem i hi hx))
        rw [eq,endsSize])
      _ = _ := by simp [Nat.mul_comm]
  have sub : P⊆S := filter_subset ..
  have leafSum : ∑ v∈P,(incidentTo L v).card=P.card := by
    calc
      _ = ∑ _∈P, 1 := sum_congr rfl (fun _ h => (mem_filter.mp h).2)
      _ = _ := by simp
  have rest : ∑ v∈S\P,(incidentTo L v).card ≤ (S\P).card*3 := calc
    _ ≤ ∑ _∈S\P, 3 := sum_le_sum (fun v _ => degree v)
    _ = _ := by simp
  have split := sum_sdiff sub (f:=fun v => (incidentTo L v).card)
  rw [card_sdiff_of_subset sub] at rest
  change 3*S.card<4*L.card at dense
  have less := card_le_card sub
  omega

#print axioms densePath
end Checkpoint125.Heawood
