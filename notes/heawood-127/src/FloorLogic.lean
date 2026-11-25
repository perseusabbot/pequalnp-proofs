import FloorTests
import PatchBudget
import LossFloor

namespace Checkpoint127.Numbers
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood Checkpoint125.Certificate
open Checkpoint126.Certificate Checkpoint126.Heawood Checkpoint127.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Bit i records membership of edge i, for i in the posted ordering. -/
def edgeMaskOf (L : Finset (Fin 21)) := word ((List.finRange 21).filter (fun i => decide (i∈L)))

theorem maskBit (L : Finset (Fin 21)) (i : Fin 21) : (edgeMaskOf L).testBit i.val=true ↔ i∈L := by
  simp [edgeMaskOf,wordBit]

private theorem bitIndex (xs : List (Fin 21)) (n : ℕ) : (word xs).testBit n=true ↔ ∃ i∈xs,i.val=n := by
  induction xs with
  | nil => simp [word]
  | cons x xs ih =>
    simp only [word,Nat.testBit_or,Bool.or_eq_true_iff,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    constructor
    · rintro (eq|⟨i,hi,eq⟩)
      · exact ⟨x,Or.inl rfl,eq⟩
      · exact ⟨i,Or.inr hi,eq⟩
    · rintro ⟨_,rfl|hi,eq⟩
      · exact Or.inl eq
      · exact Or.inr ⟨_,hi,eq⟩

private theorem remainder {es : List (Fin 21)} {L : Finset (Fin 21)} (sub : L⊆es.toFinset) :
    word es ^^^ word (es.filter (fun i => decide (i∉L)))=edgeMaskOf L := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_xor]
  by_cases h : n<21
  · let i : Fin 21 := ⟨n,h⟩
    have a : (word es).testBit n=true ↔ i∈es := wordBit es i
    have b : (word (es.filter (fun i => decide (i∉L)))).testBit n=true ↔ i∈es ∧ i∉L := by
      rw [show n=i.val from rfl,wordBit,List.mem_filter,decide_eq_true_eq]
    have c : (edgeMaskOf L).testBit n=true ↔ i∈L := maskBit L i
    have inE (hi : i∈L) := List.mem_toFinset.mp (sub hi)
    cases e : (word es).testBit n <;> cases f : (word (es.filter (fun i => decide (i∉L)))).testBit n <;>
      cases l : (edgeMaskOf L).testBit n <;> simp_all
  · have z (ys : List (Fin 21)) : (word ys).testBit n=false := by
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨i,_,eq⟩ := (bitIndex ys n).mp on
      have := i.isLt
      omega
    simp [z,edgeMaskOf]

private theorem subsetOfHit {q ew xw : ℕ} (inside : q &&& ew=q) (miss : q &&& xw=0)
    {L : Finset (Fin 21)} (eq : ew ^^^ xw=edgeMaskOf L) {i : Fin 21} (bit : q.testBit i.val=true) : i∈L := by
  have a := congrArg (fun n : ℕ => n.testBit i.val) inside
  have b := congrArg (fun n : ℕ => n.testBit i.val) miss
  simp only [Nat.testBit_and,bit,Bool.true_and,Nat.zero_testBit] at a b
  exact (maskBit ..).mp (by rw [←eq,Nat.testBit_xor,a,b]; rfl)

private theorem hit {qs ew xw} (pass : present (within qs ew) xw=true) :
    ∃ q∈qs,q &&& ew=q ∧ q &&& xw=0 := by
  obtain ⟨q,hq,hm⟩ := List.any_eq_true.mp pass
  obtain ⟨listed,inside⟩ := List.mem_filter.mp hq
  exact ⟨q,listed,eq_of_beq inside,eq_of_beq hm⟩

private def GoodPack (es : List (Fin 21)) := es.Nodup ∧ ∀ i∈es, ∀ j∈es, i≠j → Disjoint (ends i) (ends j)
private instance (es) : Decidable (GoodPack es) := by unfold GoodPack; infer_instance
private theorem packChecks : packs.all (fun es => decide (GoodPack es))=true := by decide +kernel

private theorem packLimit {w : Wire 14} (sound : ∀ z, accepts w z → predicate z)
    {es} (he : es∈packs) : (outside (edgeMaskOf (lost w)) es).length≤w.jobs.card := by
  obtain ⟨nd,apart⟩ := of_decide_eq_true (List.all_eq_true.mp packChecks es he)
  apply jobsOfMatching sound _ (nd.filter _) (fun _ hi _ hj => apart _ (List.mem_filter.mp hi).1 _ (List.mem_filter.mp hj).1)
  intro i hi
  by_contra gone
  have bit := (maskBit (lost w) i).mpr (mem_filter.mpr ⟨mem_univ i,gone⟩)
  have h := (List.mem_filter.mp hi).2
  simp [bit] at h

private theorem meetsBound {w : Wire 14} (sound : ∀ z, accepts w z → predicate z) {m v b j goal : ℕ}
    (base : j≤w.jobs.card) (check : meets goal j (edgeMaskOf (lost w)) v m b=true) :
    goal+1≤21-m+w.jobs.card+v+b := by
  rcases Bool.or_eq_true_iff.mp check with easy|choose
  · have := of_decide_eq_true easy
    omega
  · obtain ⟨es,mem,bound⟩ := List.any_eq_true.mp choose
    have := of_decide_eq_true bound
    have := packLimit sound mem
    omega

/-- A successful block audit supplies the floor and the complete boundary
list at ten losses. The two conclusions share the same circuit budget. -/
theorem bounds (audit : ∀ b<256,segment b=true) (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) :
    let w := (run 14 gs).wires.getD out default
    floorAt (missed w)≤gs.length ∧ (missed w=10 → gs.length≤26 → edgeMaskOf (lost w)∈Ten.masks) := by
  let w := (run 14 gs).wires.getD out default
  let L := lost w
  let m := L.card
  let v := (endpoints L).card
  let h := (survivors w).card
  let j := w.jobs.card
  have valid := (run_valid 14 gs).1
  have fw := port valid out
  have sound (z) (hz : accepts w z) := (spec z).mp (fw.sound z hz)
  have budget' := budget valid out spec
  have sub : survivors w⊆G.edgeFinset := budget'.sub
  have cubicBound : h≤3*j := budget'.cubic
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have split : m+h=21 := by
    have le := card_le_card sub
    change (lost w).card+(survivors w).card=21
    rw [lostSize,missed,card_sdiff_of_subset sub,tally]
    omega
  have first : h+v+j≤gs.length+1 := (terminalBudget gs out spec).1
  have path : h+v+j+(if 3*v<4*m then 1 else 0)≤gs.length+1 := by
    split_ifs with dense
    · have pay : h+v+j≤gs.length := pathBudget gs out spec (densePath _ dense)
      omega
    · omega
  obtain ⟨d,db,dv,withinSet,endsCap,packing⟩ := maskWitnessSub sound
  let es := interior d
  let xs := es.filter (fun i => decide (i∉L))
  change (vertexList d).length=v at dv
  change L⊆es.toFinset at withinSet
  change v≤2*m at endsCap
  change (retained d).length≤j at packing
  have room : m≤es.length := (card_le_card withinSet).trans (List.toFinset_card_le _)
  have nd : es.Nodup := (List.nodup_finRange _).filter _
  have eq : xs.toFinset=es.toFinset \ L := by ext i; simp [xs]
  have len : xs.length=es.length-m := by
    rw [←List.toFinset_card_of_nodup (nd.filter _),eq,card_sdiff_of_subset withinSet,List.toFinset_card_of_nodup nd]
  have member : xs∈es.sublistsLen (es.length-m) := List.mem_sublistsLen.mpr ⟨List.filter_sublist,len⟩
  let a := max (retained d).length ((21-m+2)/3)
  have cover : a≤j := max_le packing (by omega)
  let ew := word es
  let xw := word xs
  have rem : ew ^^^ xw=edgeMaskOf L := remainder withinSet
  let ss := within strong ew
  let ws := within weak ew
  let b := surcharge ss ws xw v m
  have onePatch (p : Patch) (hp : p∈patches) (inner : p.mask &&& ew=p.mask) (absent : p.mask &&& xw=0) :
      h+v+j+8≤gs.length+(if p.claw then 7 else 6) := by
    apply patchBudget gs out spec p hp
    intro i hi
    apply subsetOfHit inner absent rem
    rw [Heawood.edgeMask hp,wordBit]
    exact List.mem_toFinset.mp hi
  have pay : h+v+j+b≤gs.length+1 := by
    dsimp only [b,surcharge]
    split_ifs with strongHit weakHit dense
    · obtain ⟨q,hq,on,off⟩ := hit strongHit
      obtain ⟨p,mem,rfl⟩ := List.mem_map.mp hq
      obtain ⟨hp,cyc⟩ := List.mem_filter.mp mem
      have cost := onePatch p hp on off
      cases flag : p.claw <;> simp_all
    · obtain ⟨q,hq,on,off⟩ := hit weakHit
      rcases List.mem_append.mp hq with claw|cycle
      · obtain ⟨p,mem,rfl⟩ := List.mem_map.mp claw
        obtain ⟨hp,flag⟩ := List.mem_filter.mp mem
        have cost := onePatch p hp on off
        rw [ite_eq_left flag] at cost
        omega
      · obtain ⟨item,mem,rfl⟩ := List.mem_map.mp cycle
        have old : HasCore L := by
          refine ⟨item,mem,?_⟩
          intro i hi
          have indexed := eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp bitsCorrect _ mem) i (List.mem_finRange _))
          exact subsetOfHit on off rem (indexed ▸ (List.mem_filter.mp (List.mem_toFinset.mp hi)).2)
        have cost : h+v+j+1≤gs.length := cycleBudget gs out spec old
        omega
    · simp [dense] at path
      omega
    · omega
  have block := List.all_eq_true.mp (audit (d/64) (by omega)) (d%64) (List.mem_range.mpr (by omega))
  change checkSet (64*(d/64)+d%64)=true at block
  rw [show 64*(d/64)+d%64=d by omega] at block
  have row := List.all_eq_true.mp block m (List.mem_range.mpr (by change m<es.length+1; omega))
  have result : high m≤gs.length ∨ (m=10 ∧ edgeMaskOf L∈Ten.masks ∧ 26≤gs.length) := by
    rcases Bool.or_eq_true_iff.mp row with easy|hard
    · rcases Bool.or_eq_true_iff.mp easy with wrong|enough
      · have := of_decide_eq_true wrong
        omega
      · have good := of_decide_eq_true enough
        change high m+1≤21-m+a+(vertexList d).length+(if 3*(vertexList d).length<4*m then 1 else 0) at good
        rw [dv] at good
        exact Or.inl (by omega)
    · have detail := List.all_eq_true.mp hard xs member
      change (meets (high m) a (ew ^^^ xw) (vertexList d).length m (surcharge ss ws xw (vertexList d).length m) ||
        (decide (m=10) && Ten.masks.contains (ew ^^^ xw) &&
          meets 26 a (ew ^^^ xw) (vertexList d).length m (surcharge ss ws xw (vertexList d).length m)))=true at detail
      rw [dv,rem] at detail
      rcases Bool.or_eq_true_iff.mp detail with ok|ten
      · have good := meetsBound sound cover ok
        change high m+1≤21-m+j+v+b at good
        exact Or.inl (by omega)
      · obtain ⟨flags,yes⟩ := Bool.and_eq_true_iff.mp ten
        obtain ⟨ten,listed⟩ := Bool.and_eq_true_iff.mp flags
        have good := meetsBound sound cover yes
        change 26+1≤21-m+j+v+b at good
        exact Or.inr ⟨of_decide_eq_true ten,List.contains_iff_mem.mp listed,by omega⟩
  change floorAt (missed w)≤gs.length ∧ _
  rw [←lostSize]
  change floorAt m≤gs.length ∧ (m=10 → gs.length≤26 → edgeMaskOf L∈Ten.masks)
  rcases result with great|⟨ten,listed,gate⟩
  · by_cases ten : m=10
    · have upper : high m=27 := by simp [high,ten]
      have value : floorAt m=26 := ten ▸ (by decide)
      exact ⟨by omega,by omega⟩
    · exact ⟨by simpa [high,ten] using great,fun eq => False.elim (ten eq)⟩
  · have value : floorAt m=26 := ten ▸ (by decide)
    exact ⟨by omega,fun _ _ => listed⟩

#print axioms bounds
end Checkpoint127.Numbers
