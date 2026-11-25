import DeletionRanks3
import RebuiltPrefix

namespace Checkpoint132.Induced
open Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Binary
open Checkpoint130.Heawood Checkpoint131.Rebuild
open PEqualNP.Outside.L_meta_3004_aux.Controls

private theorem allOn : ∀ v : V,(16383 : ℕ).testBit v.val=true := by decide +kernel
private def slot (v : V) : Slot 16383 := ⟨v,allOn v⟩

private theorem fullTruth (z : Slot 16383→Bool) : accepts z ↔ predicate (fun v => z (slot v)) := by
  rw [orientation]
  exact ⟨fun ⟨x,y,h,hx,hy⟩ => ⟨x.val,y.val,h,hx,hy⟩,
    fun ⟨x,y,h,hx,hy⟩ => ⟨slot x,slot y,h,hx,hy⟩⟩

theorem programOfInducedFloor {k : ℕ} (lower : Floor 16383 k) (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) : k≤ops.length := by
  obtain ⟨gs,e,hb,hr,cap,truth⟩ := vertexProgram ops out spec
  let f (v : V) : Binary.Tree (Slot 16383) := .leaf (slot v)
  have av (v) : Ready [] (f v) := Or.inl ⟨_,rfl⟩
  have ev (z : Slot 16383→Bool) : (graft f e).eval (fun v => z v=true) ↔ accepts z :=
    (graftTruth f _ e).trans ((truth _).trans (fullTruth z).symm)
  have bound := lower _ _ (graftBuilt f (base:=[]) (by trivial) av hb) (graftReady f av hr)
    ⟨fun i => (ev i.val).mpr i.property,fun j h => j.property ((ev j.val).mp h)⟩
  simp only [List.append_nil,List.length_map] at bound
  exact bound.trans cap

theorem programTwenty (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) : 20≤ops.length :=
  programOfInducedFloor rank16383 ops out spec

theorem postedTwenty (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (h : Checkpoint122.Posted.Witness i f g tail) : 18≤tail.length := by
  let qs := Checkpoint122.Posted.codes i f g tail
  have bound := programTwenty (qs.map Checkpoint122.Posted.decode) (13+qs.length)
    (Checkpoint122.Posted.semantics _ h.2)
  simp only [List.length_map,qs,Checkpoint122.Posted.codes,List.length_cons] at bound
  omega

#print axioms programOfInducedFloor
#print axioms programTwenty
#print axioms postedTwenty
end Checkpoint132.Induced
