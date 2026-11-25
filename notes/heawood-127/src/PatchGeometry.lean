import SmallBound
import PatchData
import CycleNumbers

namespace Checkpoint127.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood Checkpoint125.Certificate Checkpoint126.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def sample (p : Patch) (r : Small.Row) (v : V) := decide (v∈p.order) && r.val.testBit (p.order.idxOf v)

private def bits (p : Patch) : List V→ℕ
  | [] => 0
  | v::vs => 2^(p.order.idxOf v) ||| bits p vs
def maskOf (p : Patch) (s : Support 14) := bits p (p.order.filter (fun v => decide (v∈s)))
private def edgeCode (p : Patch) (i : Fin 21) :=
  2^(p.order.idxOf (endpoint i false)) ||| 2^(p.order.idxOf (endpoint i true))
def allowed (p : Patch) (n : ℕ) := n=0 ∨ n∈Small.palette p.claw
private instance (p n) : Decidable (allowed p n) := by unfold allowed; infer_instance

private def ValidPatch (p : Patch) : Prop :=
  p.order.toFinset=vertices p.d ∧ (vertices p.d).card=(if p.claw then 7 else 6) ∧
  p.mask=Checkpoint126.Certificate.word (interior p.d) ∧
  ((interior p.d).map (edgeCode p)).toFinset=(Small.positives p.claw).toFinset ∧
  (∀ v : V, allowed p (maskOf p {v})) ∧
  (∀ c : V, c∉vertices p.d → allowed p (maskOf p (nbr c).toFinset))
private instance (p) : Decidable (ValidPatch p) := by unfold ValidPatch; infer_instance

private def patchAt (i : ℕ) := patches.getD i ⟨false,[],0,0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
private theorem validBlock (b : ℕ) (h : b<14) :
    (List.range 10).all (fun i => decide (ValidPatch (patchAt (10*b+i))))=true := by
  interval_cases b <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem info {p} (hp : p∈patches) : ValidPatch p := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  have size : patches.length=140 := by decide
  have h := of_decide_eq_true (List.all_eq_true.mp (validBlock (i/10) (by omega)) (i%10) (List.mem_range.mpr (by omega)))
  rw [show 10*(i/10)+i%10=i by omega] at h
  change ValidPatch (patches.getD i _) at h
  rw [List.getD_eq_getElem _ _ hi,eq] at h
  exact h

theorem orderSet {p} (hp : p∈patches) : p.order.toFinset=vertices p.d := (info hp).1
theorem vertexCount {p} (hp : p∈patches) : (vertices p.d).card=(if p.claw then 7 else 6) := (info hp).2.1
theorem edgeMask {p} (hp : p∈patches) : p.mask=Checkpoint126.Certificate.word (interior p.d) := (info hp).2.2.1

private theorem bitAt (p : Patch) (vs : List V) (i : ℕ) :
    (bits p vs).testBit i=true ↔ ∃ v∈vs,p.order.idxOf v=i := by
  induction vs with
  | nil => simp [bits]
  | cons v vs ih =>
    simp only [bits,Nat.testBit_or,Bool.or_eq_true_iff,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    constructor
    · rintro (h|⟨u,hu,eq⟩)
      · exact ⟨v,Or.inl rfl,h⟩
      · exact ⟨u,Or.inr hu,eq⟩
    · rintro ⟨_,rfl|hu,eq⟩
      · exact Or.inl eq
      · exact Or.inr ⟨_,hu,eq⟩

theorem maskTruth (p : Patch) (s : Support 14) (r : Small.Row) :
    Small.signal (maskOf p s) r=true ↔ lit s (sample p r) := by
  change ((maskOf p s &&& r.val)!=0)=true ↔ ∃ v∈s,sample p r v=true
  rw [bne_iff_ne]
  constructor
  · intro ne
    obtain ⟨i,on⟩ := Nat.exists_testBit_of_ne_zero ne
    rw [Nat.testBit_and,Bool.and_eq_true] at on
    obtain ⟨v,hv,eq⟩ := (bitAt p _ i).mp on.1
    obtain ⟨inside,hs⟩ := List.mem_filter.mp hv
    exact ⟨v,of_decide_eq_true hs,by simp [sample,inside,eq,on.2]⟩
  · rintro ⟨v,hs,on⟩ off
    obtain ⟨inside,bit⟩ := Bool.and_eq_true_iff.mp on
    have marked : (maskOf p s).testBit (p.order.idxOf v)=true := (bitAt p (p.order.filter (fun u => decide (u∈s))) (p.order.idxOf v)).mpr
      ⟨v,List.mem_filter.mpr ⟨of_decide_eq_true inside,decide_eq_true hs⟩,rfl⟩
    have bad := congrArg (fun n : ℕ => n.testBit (p.order.idxOf v)) off
    simp [Nat.testBit_and,marked,bit] at bad

theorem emptyMask (p : Patch) {s : Support 14} (off : ∀ v∈p.order,v∉s) : maskOf p s=0 := by
  have none : p.order.filter (fun v => decide (v∈s))=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨ho,hs⟩ := List.mem_filter.mp hv
    exact off _ ho (of_decide_eq_true hs)
  simp [maskOf,none,bits]

private theorem subsetBits (p : Patch) {s u : Support 14} (sub : s⊆u) :
    maskOf p s &&& maskOf p u=maskOf p s := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases h : (maskOf p s).testBit i=true
  · obtain ⟨v,hv,eq⟩ := (bitAt p _ i).mp h
    obtain ⟨inside,mem⟩ := List.mem_filter.mp hv
    have h' : (maskOf p u).testBit i=true := (bitAt p _ i).mpr
      ⟨v,List.mem_filter.mpr ⟨inside,decide_eq_true (sub (of_decide_eq_true mem))⟩,eq⟩
    simp [h,h']
  · simp_all

private theorem paletteClosed : ∀ k : Bool, ∀ x∈0::Small.palette k,
    x<128 ∧ ∀ y : Fin 128, y.val &&& x=y.val → y.val=0 ∨ y.val∈Small.palette k := by decide +kernel

theorem regularMask {p} (hp : p∈patches) {w} (sub : (interior p.d).toFinset⊆lost w)
    (hs : survivors w⊆G.edgeFinset) {s} (reg : Regular (survivors w) s) : allowed p (maskOf p s) := by
  rcases reg with tiny|⟨c,adj⟩
  · by_cases ne : s.Nonempty
    · obtain ⟨v,hv⟩ := ne
      have eq : s={v} := eq_singleton_iff_unique_mem.mpr ⟨hv,fun x hx => card_le_one.mp tiny _ hx _ hv⟩
      exact eq ▸ (info hp).2.2.2.2.1 v
    · have eq := not_nonempty_iff_eq_empty.mp ne
      exact Or.inl (emptyMask p (by simp [eq]))
  · by_cases on : c∈vertices p.d
    · apply Or.inl
      apply emptyMask
      intro v hv h
      have keep := adj v h
      have hv' : v∈vertices p.d := orderSet hp ▸ List.mem_toFinset.mpr hv
      exact missingPair sub on hv' (by simpa using hs keep) keep
    · have inc : s⊆(nbr c).toFinset := by
        intro v hv
        have near : G.Adj c v := by simpa using hs (adj v hv)
        exact List.mem_toFinset.mpr near
      have bigger := (info hp).2.2.2.2.2 c on
      have rule := paletteClosed p.claw _ (List.mem_cons.mpr bigger)
      have eq := subsetBits p inc
      have le : maskOf p s ≤ maskOf p (nbr c).toFinset := eq.symm.le.trans (Nat.and_le_right ..)
      exact rule.2 ⟨_,lt_of_le_of_lt le rule.1⟩ eq

private theorem twoBits (a b n : ℕ) :
    (2^a ||| 2^b) &&& n=(2^a ||| 2^b) ↔ n.testBit a=true ∧ n.testBit b=true := by
  constructor
  · intro eq
    have atA := congrArg (fun k : ℕ => k.testBit a) eq
    have atB := congrArg (fun k : ℕ => k.testBit b) eq
    simp [Nat.testBit_and,Nat.testBit_or] at atA atB
    exact ⟨atA,atB⟩
  · rintro ⟨ha,hb⟩
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases x : a=i <;> by_cases y : b=i <;> simp_all [Nat.testBit_and,Nat.testBit_or]

private theorem indexed (z : V→Bool) : predicate z ↔ ∃ i : Fin 21,z (endpoint i false)=true ∧ z (endpoint i true)=true := by
  rw [orientation]
  constructor
  · rintro ⟨u,v,adj,hu,hv⟩
    have m : s(u,v)∈G.edgeFinset := by simpa using adj
    rw [←indexedEdges] at m
    obtain ⟨i,_,eq⟩ := mem_image.mp m
    refine ⟨i,?_⟩
    rcases Sym2.eq_iff.mp eq with ⟨a,b⟩|⟨a,b⟩ <;> simp_all
  · rintro ⟨i,hu,hv⟩
    exact ⟨_,_,indexedAdj i,hu,hv⟩

theorem supported {p} (hp : p∈patches) (r : Small.Row) {v} (on : sample p r v=true) : v∈vertices p.d :=
  orderSet hp ▸ List.mem_toFinset.mpr (of_decide_eq_true (Bool.and_eq_true_iff.mp on).1)

theorem patchTruth {p} (hp : p∈patches) (r : Small.Row) : predicate (sample p r) ↔ Small.target p.claw r=true := by
  have graph := (info hp).2.2.2.1
  have mem (a) : a∈Small.positives p.claw ↔ ∃ i∈interior p.d,edgeCode p i=a := by
    rw [←List.mem_toFinset,←graph,List.mem_toFinset,List.mem_map]
  rw [indexed]
  constructor
  · rintro ⟨i,ha,hb⟩
    have hit := (inInterior ..).mpr ⟨supported hp r ha,supported hp r hb⟩
    apply List.any_eq_true.mpr
    refine ⟨edgeCode p i,(mem _).mpr ⟨i,hit,rfl⟩,beq_iff_eq.mpr ?_⟩
    exact (twoBits ..).mpr ⟨(Bool.and_eq_true_iff.mp ha).2,(Bool.and_eq_true_iff.mp hb).2⟩
  · intro yes
    obtain ⟨s,hs,on⟩ := List.any_eq_true.mp yes
    obtain ⟨i,hi,rfl⟩ := (mem s).mp hs
    obtain ⟨a,b⟩ := (twoBits ..).mp (eq_of_beq on)
    obtain ⟨ha,hb⟩ := (inInterior ..).mp hi
    rw [←orderSet hp,List.mem_toFinset] at ha hb
    exact ⟨i,by simp [sample,ha,a],by simp [sample,hb,b]⟩

#print axioms patchTruth
#print axioms regularMask
end Checkpoint127.Heawood
