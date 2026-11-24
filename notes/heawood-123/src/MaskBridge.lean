import CenterOptions
import CensusCount

namespace Checkpoint123.Census
open Finset SimpleGraph
open Checkpoint122.Pruning Checkpoint123.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def edgeAt (i : Fin 21) : Sym2 V :=
  let ab := edges.getD i.val (0,0)
  s(Fin.ofNat 14 ab.1,Fin.ofNat 14 ab.2)

def decode (m : ℕ) := ((indices m).map edgeAt).toFinset

private theorem edgeInj : Function.Injective edgeAt := by
  change ∀ i j : Fin 21, edgeAt i=edgeAt j → i=j
  decide +kernel

private theorem spoke : ∀ v : V, decode (spokeMask v.val)=star v := by
  set_option maxRecDepth 10000 in decide +kernel

private theorem allEdges : decode 2097151 = G.edgeFinset := by decide +kernel
private theorem allBits : ∀ i : Fin 21, (2097151 : ℕ).testBit i.val=true := by decide +kernel
private theorem oneEdge : ∀ i : Fin 21, decode (1 <<< i.val)={edgeAt i} := by
  set_option maxRecDepth 10000 in decide +kernel

private theorem indexMem (m : ℕ) (i : Fin 21) : i∈indices m ↔ m.testBit i.val=true := by
  simp [indices]

private theorem memDecode (m : ℕ) (e : Sym2 V) : e∈decode m ↔ ∃ i : Fin 21, m.testBit i.val=true ∧ edgeAt i=e := by
  simp only [decode,List.mem_toFinset,List.mem_map,indexMem]

private theorem atIndex (m : ℕ) (i : Fin 21) : edgeAt i ∈ decode m ↔ m.testBit i.val=true := by
  rw [memDecode]
  constructor
  · rintro ⟨j,hj,eq⟩
    exact edgeInj eq ▸ hj
  · exact fun yes => ⟨i,yes,rfl⟩

theorem sizeDecode (m : ℕ) : (decode m).card=(indices m).length := by
  have nd : (indices m).Nodup := (List.nodup_finRange 21).filter _
  have mnd := nd.map edgeInj
  simp [decode,List.toFinset_card_of_nodup mnd]

private theorem unionDecode (a b : ℕ) : decode (a|||b)=decode a ∪ decode b := by
  ext e
  simp only [mem_union,memDecode,Nat.testBit_or,Bool.or_eq_true]
  constructor
  · rintro ⟨i,ha|hb,eq⟩
    · exact Or.inl ⟨i,ha,eq⟩
    · exact Or.inr ⟨i,hb,eq⟩
  · rintro (⟨i,h,eq⟩|⟨i,h,eq⟩)
    · exact ⟨i,Or.inl h,eq⟩
    · exact ⟨i,Or.inr h,eq⟩

private theorem complementDecode (m : ℕ) : decode (complement m)=G.edgeFinset \ decode m := by
  ext e
  rw [← allEdges,mem_sdiff,memDecode]
  constructor
  · rintro ⟨i,yes,rfl⟩
    have off : m.testBit i.val=false := by simpa [complement,Nat.testBit_xor,allBits] using yes
    exact ⟨(atIndex _ _).mpr (allBits i),fun h => Bool.noConfusion (off.symm.trans ((atIndex _ _).mp h))⟩
  · rintro ⟨he,off⟩
    obtain ⟨i,_,rfl⟩ := (memDecode ..).mp he
    have h := Bool.eq_false_iff.mpr (fun yes => off ((atIndex m i).mpr yes))
    exact ⟨i,by simp [complement,Nat.testBit_xor,allBits,h],rfl⟩

private theorem decodedCover (cs : List V) : decode (coverMask cs)=incident cs.toFinset := by
  induction cs with
  | nil => exact (by decide +kernel : decode 0=incident ∅)
  | cons v vs ih =>
    change decode (spokeMask v.val ||| coverMask vs)=_
    rw [unionDecode,spoke,ih]
    simp [incident]

private theorem witnesses (C : Finset V) (sz : C.card=6) :
    ∃ m∈covered, decode m=incident C := by
  let cs := (List.finRange 14).filter (fun v => decide (v∈C))
  have eq : cs.toFinset=C := by ext x; simp [cs]
  have nd : cs.Nodup := (List.nodup_finRange 14).filter _
  have len : cs.length=6 := by rw [← List.toFinset_card_of_nodup nd,eq,sz]
  have member : cs∈(List.finRange 14).sublistsLen 6 := List.mem_sublistsLen.mpr ⟨List.filter_sublist,len⟩
  exact ⟨coverMask cs,List.mem_map.mpr ⟨cs,member,rfl⟩,(decodedCover cs).trans (congrArg incident eq)⟩

/-- Every six-center loss certified by the circuit proof has one of the 294 computed masks. -/
theorem encodedOption {L : Finset (Sym2 V)} (option : SixCenterOption L) :
    ∃ code∈candidates, decode code=L := by
  obtain ⟨C,sz,hL⟩ := option
  obtain ⟨m,hm,eq⟩ := witnesses C sz
  have count := sizeDecode m
  rw [eq] at count
  have add {a} (ha : a∈omissions m) : a∈candidates := List.mem_flatMap.mpr ⟨m,hm,ha⟩
  by_cases small : (incident C).card=17
  · have h : L=G.edgeFinset \ incident C := by simpa [centerOptions,small] using hL
    have size : (indices m).length=17 := count.symm.trans small
    exact ⟨complement m,add (by simp [omissions,size]),by rw [complementDecode,eq,h]⟩
  · by_cases big : (incident C).card=18
    · have shape : ∃ e ∈ incident C, insert e (G.edgeFinset \ incident C)=L := by
        simpa [centerOptions,small,big] using hL
      obtain ⟨e,he,rfl⟩ := shape
      obtain ⟨i,bit,hit⟩ := (memDecode m e).mp (eq ▸ he)
      have size : (indices m).length=18 := count.symm.trans big
      refine ⟨complement m ||| (1 <<< i.val),add ?_,?_⟩
      · simp only [omissions,size,show (18:ℕ)≠17 by decide,ite_false,ite_true,List.mem_map]
        exact ⟨i,(indexMem m i).mpr bit,rfl⟩
      · rw [unionDecode,complementDecode,oneEdge,eq,hit]
        exact union_singleton ..
    · simp [centerOptions,small,big] at hL


private theorem optionOfCode {m : ℕ} (hm : m∈candidates) : SixCenterOption (decode m) := by
  obtain ⟨cover,hc,choice⟩ := List.mem_flatMap.mp hm
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hc
  obtain ⟨sub,len⟩ := List.mem_sublistsLen.mp hcs
  have nd := (List.nodup_finRange 14).sublist sub
  refine ⟨cs.toFinset,by rw [List.toFinset_card_of_nodup nd,len],?_⟩
  let I := incident cs.toFinset
  have correct : decode (coverMask cs)=I := decodedCover cs
  have size := sizeDecode (coverMask cs)
  rw [correct] at size
  change decode m ∈ (if I.card=17 then {G.edgeFinset \ I} else
    if I.card=18 then I.image (fun e => insert e (G.edgeFinset \ I)) else ∅)
  by_cases a : I.card=17
  · have h : m=complement (coverMask cs) := by simpa [omissions,← size,a] using choice
    simp [a,h,complementDecode,correct]
  · by_cases b : I.card=18
    · obtain ⟨i,hi,eq⟩ : ∃ i∈indices (coverMask cs), complement (coverMask cs) ||| (1 <<< i.val)=m := by
        simpa [omissions,← size,a,b] using choice
      simp only [b,ite_true]
      apply mem_image.mpr
      refine ⟨edgeAt i,correct ▸ (atIndex _ _).mpr ((indexMem _ _).mp hi),?_⟩
      rw [← eq,unionDecode,complementDecode,oneEdge,correct,union_singleton]
    · simp [omissions,← size,a,b] at choice

def exactOptions := (candidates.map decode).toFinset

theorem exactOptionsIff (L : Finset (Sym2 V)) : L∈exactOptions ↔ SixCenterOption L := by
  change L∈(candidates.map decode).toFinset ↔ _
  rw [List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨m,hm,rfl⟩
    exact optionOfCode hm
  · exact encodedOption

private theorem decodeInj {x y : ℕ} (hx : x<2097152) (hy : y<2097152) (eq : decode x=decode y) : x=y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<21
  · let t : Fin 21 := ⟨i,hi⟩
    apply Bool.eq_iff_iff.mpr
    exact ((atIndex x t).symm.trans (show edgeAt t∈decode x ↔ edgeAt t∈decode y by rw [eq])).trans (atIndex y t)
  · have big : 2^21≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (hx.trans_le big),Nat.testBit_lt_two_pow (hy.trans_le big)]

/-- This counts the graph edge sets themselves. It does not assert realization by circuits. -/
theorem exactOptionCount : exactOptions.card=294 := by
  obtain ⟨_,_,_,length,distinct,checked⟩ := counts
  have small (x) (hx : x∈candidates) : x<2097152 :=
    (of_decide_eq_true (List.all_eq_true.mp checked x hx)).1
  have nodup : (candidates.map decode).Nodup := List.Nodup.map_on
    (fun x hx y hy eq => decodeInj (small x hx) (small y hy) eq) distinct
  change (candidates.map decode).toFinset.card=294
  rw [List.toFinset_card_of_nodup nodup,List.length_map,length]

private theorem smallProfile (j b t e d l : ℕ) (h : [j,b,t,e,d,l]∈profiles) :
    25≤l ∧ (d=2 → j=6) := by
  simp [profiles] at h
  omega

/-- Two nested ANDs in the four-loss case force the six-product branch of the census. -/
theorem twoCutMasks (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) (loss : missed ((run 14 gs).wires.getD out default)=4)
    (two : (run 14 gs).dropped=2) :
    ∃ code∈candidates, decode code=G.edgeFinset \ survivors ((run 14 gs).wires.getD out default) := by
  have shapes := fourProfiles gs out spec short loss
  have six := (smallProfile _ _ _ _ _ _ shapes).2 two
  have fw := port (run_valid 14 gs).1 out
  exact encodedOption (optionsOfSix (fun z h => (spec z).mp (fw.sound z h)) six loss)

/-- At 24 gates or fewer, even a four-edge loss is impossible. -/
theorem fiveBelow25 (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤24) : 5 ≤ missed ((run 14 gs).wires.getD out default) := by
  have h := fourLost gs out spec (by omega)
  by_contra! no
  have eq : missed ((run 14 gs).wires.getD out default)=4 := by omega
  have low := (smallProfile _ _ _ _ _ _ (fourProfiles gs out spec (by omega) eq)).1
  omega

#print axioms encodedOption
#print axioms exactOptionsIff
#print axioms exactOptionCount
#print axioms twoCutMasks
#print axioms fiveBelow25
end Checkpoint123.Census
