import PatternBlocks

namespace Checkpoint125.Heawood
open PatternProof PEqualNP.Outside.L_meta_3004_aux.Controls

private theorem stream (bs : List (List (List V))) :
    bs.flatten.flatMap fromCenters = (bs.map (fun xs => xs.flatMap fromCenters)).flatten := by
  induction bs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatten_cons,List.flatMap_append,List.map_cons,ih]

private theorem wordList :
    eightWords = ((List.range 63).map (fun b => BoundaryData.blocks.getD b [])).flatten.eraseDups := by
  calc
    _ = (((List.range 63).map part).map fun xs => xs.flatMap fromCenters).flatten.eraseDups := by
      rw [←stream,chunks]
      rfl
    _ = _ := by
      rw [List.map_map]
      apply congrArg (fun ls : List (List ℕ) => ls.flatten.eraseDups)
      exact List.map_congr_left (fun b hb => checked b (List.mem_range.mp hb))


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem eightCount : eightWords.length=357 := by
  rw [wordList]
  decide +kernel

private def sightings := BoundaryData.sortedMasks.zip BoundaryData.origins

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem evidence :
    sightings.map Prod.fst=BoundaryData.sortedMasks ∧
    sightings.all (fun p => decide (p.2<63 ∧ p.1∈BoundaryData.blocks.getD p.2 []))=true := by
  decide +kernel

private theorem sortedSize : BoundaryData.sortedMasks.length=357 := by decide +kernel
private theorem increasing : BoundaryData.sortedMasks.IsChain (· < ·) := by decide +kernel

/-- The ascending published list has exactly the same members as the
enumerated list. Each listed mask has a witness block of five-center sets. -/
theorem eightList : eightWords.toFinset=BoundaryData.sortedMasks.toFinset := by
  have sub : BoundaryData.sortedMasks.toFinset⊆eightWords.toFinset := by
    intro w hw
    have member := List.mem_toFinset.mp hw
    rw [←evidence.1] at member
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp member
    obtain ⟨lt,hit⟩ := of_decide_eq_true (List.all_eq_true.mp evidence.2 p hp)
    rw [wordList]
    apply List.mem_toFinset.mpr
    apply List.mem_eraseDups.mpr
    apply List.mem_flatten.mpr
    exact ⟨_,List.mem_map.mpr ⟨p.2,List.mem_range.mpr lt,rfl⟩,hit⟩
  have nodup : BoundaryData.sortedMasks.Nodup :=
    (List.isChain_iff_pairwise.mp increasing).imp (fun h => Nat.ne_of_lt h)
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le sub
  rw [List.toFinset_card_of_nodup nodup,sortedSize]
  exact eightWords.toFinset_card_le.trans_eq eightCount

#print axioms eightList
#print axioms eightCount
end Checkpoint125.Heawood
