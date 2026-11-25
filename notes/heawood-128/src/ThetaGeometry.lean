import ThetaShapes
import Mathlib.Data.List.Sublists

namespace Checkpoint128.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood Checkpoint125.Contract
open Checkpoint125.Certificate Checkpoint126.Heawood Checkpoint127.Heawood Checkpoint128.Theta
open PEqualNP.Outside.L_meta_3004_aux.Controls

def code (p : Shape) (v : V) := p.codes.getD v.val 0
def sample (p : Shape) (row : ℕ) (v : V) := (code p v &&& row)!=0
private def merge (p : Shape) : List V→ℕ
  | [] => 0
  | v::vs => code p v ||| merge p vs
def wordOf (p : Shape) (s : Support 14) := merge p ((List.finRange 14).filter (fun v => decide (v∈s)))

private theorem mergeOn (p : Shape) (row : ℕ) (vs : List V) :
    merge p vs &&& row≠0 ↔ ∃ v∈vs,sample p row v=true := by
  induction vs with
  | nil => simp [merge]
  | cons a vs ih =>
    have split : (code p a ||| merge p vs) &&& row≠0 ↔ code p a &&& row≠0 ∨ merge p vs &&& row≠0 := by
      rw [Nat.and_or_distrib_right,ne_eq,Nat.or_eq_zero_iff]
      tauto
    rw [merge,split,ih]
    simp [sample]


theorem wordOn (p : Shape) (s : Support 14) (row : ℕ) :
    ((wordOf p s &&& row) != 0)=true ↔ lit s (sample p row) := by
  simp [wordOf,mergeOn,lit]

private def near (p : Shape) (c : V) := (nbr c).filter (fun v =>
  !(p.domain.testBit c.val && p.domain.testBit v.val))
private def indexedTrue (p : Shape) (row : ℕ) := (List.finRange 21).any (fun i =>
  sample p row (endpoint i false) && sample p row (endpoint i true))
private def Good (p : Shape) : Prop :=
  (interior p.domain).toFinset=decoded p.mask ∧
  (∀ v : V, code p v≠0 → v∈vertices p.domain) ∧
  (∀ v : V, v∈vertices p.domain ↔ p.domain.testBit v.val=true) ∧
  (∀ w∈pos,indexedTrue p w=true) ∧ (∀ w∈neg,indexedTrue p w=false) ∧
  (∀ v : V, wordOf p {v}∈0::masks) ∧
  ∀ c : V, ∀ l∈(near p c).sublists,wordOf p l.toFinset∈0::masks
private instance (p) : Decidable (Good p) := by unfold Good; infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
private theorem blockGood (b : ℕ) (h : b<14) :
    (List.range 6).all (fun i => decide (Good (shapes.getD (6*b+i) ⟨0,0,[]⟩)))=true := by
  interval_cases b <;> decide +kernel

private theorem good {p} (h : p∈shapes) : Good p := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  have size : shapes.length=84 := by decide +kernel
  have ok := of_decide_eq_true (List.all_eq_true.mp (blockGood (i/6) (by omega)) (i%6) (List.mem_range.mpr (by omega)))
  rw [show 6*(i/6)+i%6=i by omega,List.getD_eq_getElem _ _ hi,eq] at ok
  exact ok

theorem shapeOf {m} (hm : m∈Checkpoint127.Ten.masks) : ∃ p∈shapes,p.mask=m := by
  have eq : shapes.map Shape.mask=Checkpoint127.Ten.masks := by decide +kernel
  exact List.mem_map.mp (eq ▸ hm)

theorem interiorEq {p} (h : p∈shapes) : (interior p.domain).toFinset=decoded p.mask := (good h).1

theorem inside {p} (h : p∈shapes) (row) {v} (on : sample p row v=true) : v∈vertices p.domain := by
  apply (good h).2.1 v
  intro off
  simp [sample,off] at on

private theorem indexedIff (p : Shape) (row : ℕ) : indexedTrue p row=true ↔ predicate (sample p row) := by
  rw [orientation]
  constructor
  · intro hit
    obtain ⟨i,_,live⟩ := List.any_eq_true.mp hit
    exact ⟨_,_,indexedAdj i,(Bool.and_eq_true_iff.mp live).1,(Bool.and_eq_true_iff.mp live).2⟩
  · rintro ⟨u,v,adj,a,b⟩
    have he : s(u,v)∈G.edgeFinset := by simpa using adj
    rw [←indexedEdges] at he
    obtain ⟨i,_,eq⟩ := mem_image.mp he
    apply List.any_eq_true.mpr
    refine ⟨i,List.mem_finRange _,?_⟩
    rcases Sym2.eq_iff.mp eq with ⟨x,y⟩|⟨x,y⟩ <;> simp_all

theorem samplePos {p} (h : p∈shapes) {w} (hw : w∈pos) : predicate (sample p w) :=
  (indexedIff ..).mp ((good h).2.2.2.1 w hw)
theorem sampleNeg {p} (h : p∈shapes) {w} (hw : w∈neg) : ¬predicate (sample p w) := by
  intro yes
  have hit := (indexedIff ..).mpr yes
  rw [(good h).2.2.2.2.1 w hw] at hit
  contradiction

theorem labelWord {p w} (h : p∈shapes) (sub : (interior p.domain).toFinset⊆lost w)
    (hs : survivors w⊆G.edgeFinset) {s} (regular : Regular (survivors w) s) : wordOf p s∈0::masks := by
  rcases regular with tiny|⟨c,adj⟩
  · by_cases live : s.Nonempty
    · obtain ⟨v,hv⟩ := live
      have eq : s={v} := eq_singleton_iff_unique_mem.mpr ⟨hv,fun _ ha => card_le_one.mp tiny _ ha _ hv⟩
      exact eq ▸ (good h).2.2.2.2.2.1 v
    · have eq := not_nonempty_iff_eq_empty.mp live
      simp [eq,wordOf,merge]
  · let l := (near p c).filter (fun v => decide (v∈s))
    have mem : l∈(near p c).sublists := List.mem_sublists.mpr (List.filter_sublist ..)
    have enc : l.toFinset=s := by
      ext v
      simp only [l,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
      intro hv
      have keep := adj v hv
      have edge : G.Adj c v := by simpa using hs keep
      apply List.mem_filter.mpr
      refine ⟨edge,?_⟩
      suffices off : ¬(p.domain.testBit c.val && p.domain.testBit v.val)=true by
        cases bit : (p.domain.testBit c.val && p.domain.testBit v.val) <;> simp_all
      intro both
      obtain ⟨cIn,vIn⟩ := Bool.and_eq_true_iff.mp both
      have point := (good h).2.2.1
      exact missingPair sub ((point c).mpr cIn) ((point v).mpr vIn) edge keep
    exact enc ▸ (good h).2.2.2.2.2.2 c l mem

private def CountInfo (p : Shape) : Prop := (vertices p.domain).card=9 ∧
  ∀ v : V, v∉vertices p.domain → wordOf p {v}=0
private instance (p) : Decidable (CountInfo p) := by unfold CountInfo; infer_instance

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem countInfo {p} (hp : p∈shapes) : (vertices p.domain).card=9 ∧
    ∀ v : V, v∉vertices p.domain → wordOf p {v}=0 := by
  have all : shapes.all (fun q => decide (CountInfo q))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ hp)

#print axioms labelWord
end Checkpoint128.Heawood
