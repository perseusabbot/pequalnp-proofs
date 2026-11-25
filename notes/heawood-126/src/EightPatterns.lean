import EightBoundary
import FiveCenters

namespace Checkpoint125.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def coveredIndices (cs : List V) := (List.finRange 21).filter fun i =>
  cs.contains (endpoint i false) || cs.contains (endpoint i true)
def edgeWord (L : Finset (Fin 21)) := ∑ i∈L, 2^i.val

private def vertexWord : List (Fin 21) → ℕ
  | [] => 0
  | i::xs => (2^(endpoint i false).val ||| 2^(endpoint i true).val) ||| vertexWord xs

private theorem vertexBit (xs : List (Fin 21)) (v : V) :
    (vertexWord xs).testBit v.val=true ↔ v∈endpoints xs.toFinset := by
  induction xs with
  | nil => simp [vertexWord,endpoints]
  | cons i xs ih =>
    simp only [vertexWord,Nat.testBit_or,Bool.or_eq_true_iff,Nat.testBit_two_pow,
      decide_eq_true_eq,←Fin.ext_iff,ih,List.toFinset_cons,endpoints,biUnion_insert,mem_union,
      ends,mem_insert,mem_singleton]
    tauto

private theorem vertexCount (xs : List (Fin 21)) :
    (Certificate.vertexList (vertexWord xs)).length=(endpoints xs.toFinset).card := by
  have eq : (Certificate.vertexList (vertexWord xs)).toFinset=endpoints xs.toFinset := by
    ext v
    simp [Certificate.vertexList,vertexBit]
  rw [←eq]
  exact (List.toFinset_card_of_nodup (l:=Certificate.vertexList _) ((List.nodup_finRange _).filter _)).symm

/-- With five centers, at least the six edges avoiding all centers must be
missing. Complete those edges to an eight-edge omission inside eight vertices. -/
def fromCenters (cs : List V) : List ℕ :=
  let outsideC := outside cs
  if outsideC.length>8 then [] else
    ((coveredIndices cs).sublistsLen (8-outsideC.length)).filterMap fun extra =>
      let xs := outsideC++extra
      if (Certificate.vertexList (vertexWord xs)).length=8 then some (edgeWord xs.toFinset) else none

def eightWords := (((List.finRange 14).sublistsLen 5).flatMap fromCenters).eraseDups

/-- An eight-loss realization has an omitted edge mask in this explicit list. -/
theorem eightPatterns (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) (eight : missed ((run 14 gs).wires.getD out default)=8) :
    edgeWord (lost ((run 14 gs).wires.getD out default))∈eightWords := by
  classical
  let w := (run 14 gs).wires.getD out default
  let L := lost w
  change edgeWord L∈eightWords
  obtain ⟨_,v8,j5,_⟩ := eightProfile gs out spec short eight
  change (endpoints L).card=8 at v8
  change w.jobs.card=5 at j5
  have loss : L.card=8 := (lostSize w).trans eight
  have valid := (run_valid 14 gs).1
  have fw := port valid out
  have sub : survivors w⊆G.edgeFinset := (budget valid out spec).sub
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have count : (survivors w).card=13 := by
    change missed w=8 at eight
    rw [missed,card_sdiff_of_subset sub,tally] at eight
    omega
  obtain ⟨C,small,cover⟩ := Checkpoint123.Heawood.centers (w:=w) (fun z h => (spec z).mp (fw.sound z h))
  have degree : ∀ v : V, (star v).card=3 := by decide +kernel
  have cap : (incident C).card ≤ 3*C.card := calc
    (incident C).card ≤ ∑ v∈C, (star v).card := card_biUnion_le
    _ = 3*C.card := by simp [degree,Nat.mul_comm]
  have fit := card_le_card cover
  have cc : C.card=5 := by omega
  let cs := (List.finRange 14).filter (fun v => decide (v∈C))
  have eq : cs.toFinset=C := by ext v; simp [cs]
  have cn : cs.Nodup := (List.nodup_finRange _).filter _
  have clen : cs.length=5 := by rw [←List.toFinset_card_of_nodup cn,eq,cc]
  have member : cs∈(List.finRange 14).sublistsLen 5 := List.mem_sublistsLen.mpr ⟨List.filter_sublist,clen⟩
  have aSub (i) (hi : i∈outside cs) : i∈L := by
    have sides : endpoint i false∉C ∧ endpoint i true∉C := by simpa [cs,outside] using hi
    apply mem_filter.mpr
    refine ⟨mem_univ _,fun live => ?_⟩
    obtain ⟨v,hv,spoke⟩ := mem_biUnion.mp (cover live)
    obtain ⟨u,_,e⟩ := mem_image.mp spoke
    rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact sides.1 hv
    · exact sides.2 hv
  have partition (i) : i∈coveredIndices cs ↔ i∉outside cs := by simp [coveredIndices,outside]; tauto
  let more := (coveredIndices cs).filter (fun i => decide (i∈L))
  have listed (i) : i∈more ↔ i∉outside cs ∧ i∈L := by simp only [more,List.mem_filter,decide_eq_true_eq,partition]
  have total : (outside cs++more).toFinset=L := by
    ext i
    simp only [List.mem_toFinset,List.mem_append,listed]
    exact ⟨fun h => h.elim (aSub i) And.right,fun h => or_iff_not_imp_left.mpr (fun h' => ⟨h',h⟩)⟩
  have nd : (outside cs++more).Nodup := List.nodup_append'.mpr ⟨(List.nodup_finRange _).filter _,
    ((List.nodup_finRange _).filter _).filter _,fun _ h h' => ((listed _).mp h').1 h⟩
  have size := List.toFinset_card_of_nodup nd
  rw [total,loss,List.length_append] at size
  have takeMore : more∈(coveredIndices cs).sublistsLen (8-(outside cs).length) :=
    List.mem_sublistsLen.mpr ⟨List.filter_sublist,by omega⟩
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨cs,member,?_⟩
  unfold fromCenters
  rw [ite_eq_right (show ¬(outside cs).length>8 by omega)]
  exact List.mem_filterMap.mpr ⟨more,takeMore,by
    dsimp only
    rw [vertexCount,total,ite_eq_left v8]⟩

#print axioms eightPatterns
end Checkpoint125.Heawood
