import ForcedInputs
import FourProfiles
import MatchingTable

namespace Checkpoint125.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Certificate
open PEqualNP.Outside.L_meta_3004_aux.Controls

private def pack : List V → ℕ
  | [] => 0
  | x::xs => 2^x.val ||| pack xs

private theorem represents (xs : List V) (v : V) : (pack xs).testBit v.val=true ↔ v∈xs := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih =>
    simp only [pack,Nat.testBit_or,Bool.or_eq_true_iff,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    simp only [←Fin.ext_iff]
    tauto

private theorem bounded (xs : List V) : pack xs<2^14 := by
  induction xs with
  | nil => decide
  | cons x xs ih => exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide) x.isLt) ih

theorem samePairs : ∀ i : Fin 21,
    (pairAt i).1=endpoint i false ∧ (pairAt i).2=endpoint i true := by decide +kernel

private def Good (es : List (Fin 21)) := es.Nodup ∧ ∀ i∈es, ∀ j∈es, i≠j → Disjoint (ends i) (ends j)
private instance (es) : Decidable (Good es) := by unfold Good; infer_instance
private theorem disjointMatchings : ∀ n : Fin 32, Good (matchings.getD n.val []) := by
  set_option maxRecDepth 6000 in
  set_option maxHeartbeats 0 in
  decide +kernel

theorem jobsOfMatching {w : Wire 14} (sound : ∀ z, accepts w z → predicate z)
    (es : List (Fin 21)) (nodup : es.Nodup) (apart : ∀ i∈es, ∀ j∈es,i≠j → Disjoint (ends i) (ends j))
    (live : ∀ i∈es, edge i∈survivors w) : es.length≤w.jobs.card := by
  classical
  obtain ⟨C,small,cover⟩ := Checkpoint123.Heawood.centers sound
  let E := es.toFinset
  have assign (i : E) : ∃ v∈C, v∈ends i.val := by
    obtain ⟨v,hv,spoke⟩ := mem_biUnion.mp (cover (live i.val (List.mem_toFinset.mp i.property)))
    obtain ⟨u,_,eq⟩ := mem_image.mp spoke
    refine ⟨v,hv,?_⟩
    rcases Sym2.eq_iff.mp eq with ⟨eq,_⟩|⟨eq,_⟩ <;> simp [ends,eq]
  choose v vc ve using assign
  let f (i : E) : C := ⟨v i,vc i⟩
  have distinct : Function.Injective f := by
    intro i j h
    by_contra ne
    have ij : i.val≠j.val := fun h => ne (Subtype.ext h)
    have dis := apart _ (List.mem_toFinset.mp i.property) _ (List.mem_toFinset.mp j.property) ij
    have same : v i=v j := congrArg Subtype.val h
    exact disjoint_left.mp dis (ve i) (same ▸ ve j)
  have count := Fintype.card_le_of_injective f distinct
  simp only [Fintype.card_coe] at count
  have eq : E.card=es.length := List.toFinset_card_of_nodup nodup
  omega

private theorem matchingBound {w : Wire 14} (sound : ∀ z, accepts w z → predicate z)
    (d : ℕ) (live : ∀ i∈retained d, edge i∈survivors w) : (retained d).length≤w.jobs.card := by
  have fits : choice d<32 := Nat.mod_lt _ (by decide)
  obtain ⟨nodup,apart⟩ := disjointMatchings ⟨choice d,fits⟩
  exact jobsOfMatching sound _ (nodup.filter _) (fun _ hi _ hj =>
    apart _ (List.mem_filter.mp hi).1 _ (List.mem_filter.mp hj).1) live

/-- Encode the actual endpoint set and pass a verified packing of surviving
edges to the numerical bound. -/
theorem maskWitnessSub {w : Wire 14} (sound : ∀ z, accepts w z → predicate z) :
    let L := lost w
    let D := endpoints L
    ∃ d<16384, (vertexList d).length=D.card ∧ L⊆(interior d).toFinset ∧
      D.card≤2*L.card ∧ (retained d).length≤w.jobs.card := by
  classical
  let L := lost w
  let D := endpoints L
  let d := pack D.toList
  have bits (v : V) : d.testBit v.val=true ↔ v∈D := (represents D.toList v).trans mem_toList
  have eq : (vertexList d).toFinset=D := by ext v; simp [vertexList,bits]
  have length : (vertexList d).length=D.card := by
    rw [←eq]
    exact (List.toFinset_card_of_nodup (l:=vertexList d) ((List.nodup_finRange _).filter _)).symm
  have contained {i} (hi : i∈L) : inside d i=true := by
    rw [inside,(samePairs i).1,(samePairs i).2,Bool.and_eq_true]
    exact ⟨(bits _).mpr (mem_biUnion.mpr ⟨i,hi,by simp [ends]⟩),
      (bits _).mpr (mem_biUnion.mpr ⟨i,hi,by simp [ends]⟩)⟩
  have sub : L⊆(interior d).toFinset := fun i hi => List.mem_toFinset.mpr
    (List.mem_filter.mpr ⟨List.mem_finRange _,contained hi⟩)
  have degree : D.card≤2*L.card := calc
    D.card ≤ ∑ i∈L,(ends i).card := card_biUnion_le
    _ = 2*L.card := by simp [endsSize,Nat.mul_comm]
  refine ⟨d,bounded _,length,sub,degree,matchingBound sound d ?_⟩
  intro i hi
  by_contra gone
  have on := contained (i:=i) (show i∈L from mem_filter.mpr ⟨mem_univ i,gone⟩)
  have off := (List.mem_filter.mp hi).2
  simp [on] at off

theorem maskWitness {w : Wire 14} (sound : ∀ z, accepts w z → predicate z) :
    let L := lost w
    let D := endpoints L
    ∃ d<16384, (vertexList d).length=D.card ∧ L.card≤(interior d).length ∧
      D.card≤2*L.card ∧ (retained d).length≤w.jobs.card := by
  obtain ⟨d,h,v,sub,two,pack⟩ := maskWitnessSub sound
  exact ⟨d,h,v,(card_le_card sub).trans (List.toFinset_card_le _),two,pack⟩

#print axioms maskWitness
end Checkpoint125.Heawood
