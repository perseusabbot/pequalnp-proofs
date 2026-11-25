import TwentyTwo

namespace Checkpoint131.Deletion
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def ports : List ℕ := [1,2,4,8,16,32,128,256,512,1024,2048,4096,8192]
def posRows : List ℕ := [129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128]
def negRows : List ℕ := [63,180,314,432,541,660,792,1038,1290,1548,2087,2212,2338,2565,3078,3716,4115,4370,4625,5008,6147,7426,8233,8488,8713,9992,10273,10656,14849,16256]
def placements : List (List ℕ) := [
  [0,1,32,4,16,8,2,256,512,128,2048,8192,4096,1024],
  [1,0,8,4,16,32,2,256,128,512,1024,8192,4096,2048],
  [1,2,0,8,32,16,4,128,256,8192,1024,4096,2048,512],
  [1,4,2,0,16,32,8,256,128,4096,1024,2048,512,8192],
  [1,2,32,8,0,4,16,128,1024,8192,256,2048,4096,512],
  [1,2,16,8,4,0,32,128,1024,512,256,4096,2048,8192],
  [1,2,4,8,16,32,0,128,256,512,1024,2048,4096,8192],
  [256,512,1024,2048,4096,8192,128,0,1,2,4,8,16,32],
  [256,128,2048,1024,4096,8192,512,1,0,2,4,32,16,8],
  [128,256,8192,1024,4096,2048,512,1,2,0,8,32,16,4],
  [256,128,4096,1024,2048,512,8192,1,4,2,0,16,32,8],
  [128,1024,8192,256,2048,4096,512,1,2,32,8,0,4,16],
  [128,1024,512,256,4096,2048,8192,1,2,16,8,4,0,32],
  [128,256,512,1024,2048,4096,8192,1,2,4,8,16,32,0]]

def Legal (q : List ℕ) : Prop := (∀ v : V,code q v∈0::ports) ∧
  (∀ r∈posRows,edgeOn (liftRow q r)=true) ∧ (∀ r∈negRows,edgeOn (liftRow q r)=false)
instance (q) : Decidable (Legal q) := by unfold Legal; infer_instance

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem legalPlacement {q} (h : q∈placements) : Legal q := by
  have all : placements.all (fun r => decide (Legal r))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ h)

theorem deletes : ∀ x : V,∃ q∈placements,code q x=0 := by decide +kernel

def low (op : Bool) (u y v : V) := decide (v=u) || (op && decide (v=y))
def high (op : Bool) (u x y v : V) := decide (v=x) || low op u y v

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem witness : ∀ x y : V,x≠y → ∀ op : Bool,∃ u : V,edgeOn (high op u x y)=true ∧
    edgeOn (low op u y)=false ∧ high op u x y y=op ∧ low op u y y=op := by decide +kernel

#print axioms legalPlacement
#print axioms deletes
#print axioms witness
end Checkpoint131.Deletion
