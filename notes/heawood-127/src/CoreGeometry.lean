import CycleData
import CherryBound
import PathObstruction
import VertexMasks

namespace Checkpoint126.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood Checkpoint125.Certificate
open PEqualNP.Outside.L_meta_3004_aux.Controls

def vertices (d : ℕ) : Finset V := (vertexList d).toFinset
def clip (d : ℕ) (a : V→Bool) (v : V) := if v∈vertices d then a v else false
def HasCore (L : Finset (Fin 21)) := ∃ q∈cores, (interior q.1).toFinset⊆L

theorem inInterior (d) (i : Fin 21) :
    i∈interior d ↔ endpoint i false∈vertices d ∧ endpoint i true∈vertices d := by
  simp [Checkpoint125.Certificate.interior,inside,vertices,vertexList,(samePairs i).1,(samePairs i).2]

private def Witness (d : ℕ) (x y : V) (h : Bool) (u : V) : Prop :=
  u∈vertices d ∧ G.Adj x u ∧ (y≠x → (h=false → u≠y) ∧ (h=true → y∈vertices d → ¬G.Adj u y))
private instance (d x y h u) : Decidable (Witness d x y h u) := by unfold Witness; infer_instance

private def Rule (d : ℕ) : Prop :=
  2≤(vertices d).card ∧
  (∀ x∈vertexList d, ∃ i∈interior d, x∈ends i) ∧
  (∀ x∈vertexList d, ∀ (y : V) (h : Bool), ∃ u∈nbr x, Witness d x y h u) ∧
  (∀ c : V, ∃ p∈paths, (∀ v∈p.vertices, v∈vertices d) ∧
    (c∈vertices d ∨ (¬G.Adj c p.b ∧ ¬G.Adj c p.c)))
private instance (d) : Decidable (Rule d) := by
  unfold Rule
  exact @instDecidableAnd _ _ (by infer_instance) (@instDecidableAnd _ _ (by infer_instance)
    (@instDecidableAnd _ _ (by infer_instance) (by infer_instance)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
private theorem checked : cores.all (fun q => decide (Rule q.1))=true := by decide +kernel

private theorem info {q} (hq : q∈cores) : Rule q.1 := of_decide_eq_true (List.all_eq_true.mp checked q hq)

theorem atLeastTwo {q} (hq : q∈cores) : 2≤(vertices q.1).card := (info hq).1

theorem endpointsSub {q} (hq : q∈cores) {L} (sub : (interior q.1).toFinset⊆L) :
    vertices q.1⊆endpoints L := by
  intro x hx
  obtain ⟨i,hi,mem⟩ := (info hq).2.1 x (List.mem_toFinset.mp hx)
  exact mem_biUnion.mpr ⟨i,sub (List.mem_toFinset.mpr hi),mem⟩

theorem missingPair {d w} (sub : (interior d).toFinset⊆lost w) {u v}
    (hu : u∈vertices d) (hv : v∈vertices d) (adj : G.Adj u v) : s(u,v)∉survivors w := by
  have edgeIn : s(u,v)∈G.edgeFinset := by simpa using adj
  rw [←indexedEdges] at edgeIn
  obtain ⟨i,_,eq⟩ := mem_image.mp edgeIn
  have mem : i∈interior d := by
    apply (inInterior ..).mpr
    rcases Sym2.eq_iff.mp eq with ⟨a,b⟩|⟨a,b⟩ <;> simp_all
  exact eq ▸ (mem_filter.mp (sub (List.mem_toFinset.mpr mem))).2

theorem domain {d w} (sound : ∀ z, accepts w z → predicate z) (sub : (interior d).toFinset⊆lost w)
    {z} (inside : ∀ v, z v=true → v∈vertices d) : Checkpoint125.Contract.Domain w.jobs z := by
  rintro p hp ⟨⟨u,hu,zu⟩,v,hv,zv⟩
  exact missingPair sub (inside u zu) (inside v zv) ((describe sound).2 p hp u hu v hv)
    ((in_survivors w _).mpr ⟨p,hp,u,hu,v,hv,rfl⟩)

theorem safePath {q} (hq : q∈cores) {w} (sub : (interior q.1).toFinset⊆lost w)
    (S : Support 14) (regular : Regular (survivors w) S) (hs : survivors w⊆G.edgeFinset) :
    ∃ p∈paths, (∀ v∈p.vertices, v∈vertices q.1) ∧ (S.card≤1 ∨ (p.b∉S ∧ p.c∉S)) := by
  rcases regular with small|⟨c,adj⟩
  · obtain ⟨p,hp,ok,_⟩ := (info hq).2.2.2 0
    exact ⟨p,hp,ok,Or.inl small⟩
  · obtain ⟨p,hp,ok,avoid⟩ := (info hq).2.2.2 c
    have miss (v : V) (hv : v∈p.vertices) (away : c∈vertices q.1 ∨ ¬G.Adj c v) : v∉S := by
      intro h
      have live := adj v h
      have a : G.Adj c v := by simpa using hs live
      exact away.elim (fun hc => missingPair sub hc (ok v hv) a live) (fun no => no a)
    exact ⟨p,hp,ok,Or.inr ⟨miss _ (by simp [Chain.vertices]) (avoid.imp_right And.left),
      miss _ (by simp [Chain.vertices]) (avoid.imp_right And.right)⟩⟩

theorem robust {q} (hq : q∈cores) : Cherry.Robust (vertices q.1) (fun a => predicate (clip q.1 a)) := by
  intro x hx y h
  obtain ⟨u,_,hu,adj,can⟩ := (info hq).2.2.1 x (List.mem_toFinset.mp hx) y h
  let b := fun v : V => decide (v=u ∨ (y≠x ∧ h=true ∧ v=y))
  let a := fun v : V => decide (v=x) || b v
  have yes : predicate (clip q.1 a) := (orientation _).mpr
    ⟨x,u,adj,by simp [clip,hx,a],by simp [clip,hu,a,b]⟩
  have no : ¬predicate (clip q.1 b) := by
    intro hpos
    obtain ⟨i,j,ij,vi,vj⟩ := (orientation _).mp hpos
    have active {v} (hv : clip q.1 b v=true) : v∈vertices q.1 ∧ (v=u ∨ (y≠x ∧ h=true ∧ v=y)) := by
      by_cases inside : v∈vertices q.1 <;> simp_all [clip,b]
    obtain ⟨si,rfl|⟨ne,hh,rfl⟩⟩ := active vi <;> obtain ⟨sj,rfl|⟨ne',hh',rfl⟩⟩ := active vj
    · exact ij.ne rfl
    · exact (can ne').2 hh' sj ij
    · exact (can ne).2 hh si ij.symm
    · exact ij.ne rfl
  refine ⟨a,b,yes,no,fun v ne => by simp [a,ne],?_⟩
  intro ne
  cases h
  · have nd := ((can ne).1 rfl).symm
    simp [a,b,ne,nd]
  · simp [a,b,ne]

#print axioms robust
#print axioms safePath
end Checkpoint126.Heawood
