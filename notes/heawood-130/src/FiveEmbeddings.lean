import ProjectedBlock14
import EdgeRows

namespace Checkpoint130.Heawood
open Finset Checkpoint128.Heawood Checkpoint129.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def five : Screen := ⟨⟨32751,11679,[1,2,4,8,16,0,0,128,256,0,1024,2048,0,8192]⟩,15,[4,16,18],[1,2,4,8,16,128,256,1024,2048,2304,8192],[129,257,1025,130,8194,260,8196,136,2056,1040,2064,8208],[31,148,282,400,1038,1290,2055,3078,3204,3330,8201,9480,10241,11648]⟩

theorem sameFive : block14[6]?=some five := by rfl

def embeddings : List (List ℕ) := [
  [0,0,4,2,1,16,8,0,0,2048,1024,128,8192,256],
  [1024,256,0,128,8192,2048,0,1,0,0,16,2,8,4],
  [0,256,128,8192,1024,0,2048,4,8,0,0,16,2,1],
  [256,2048,128,0,0,8192,1024,0,1,16,4,0,2,8],
  [1,0,2,16,0,4,8,1024,128,0,256,2048,8192,0],
  [1,4,0,0,8,2,16,256,1024,8192,128,2048,0,0],
  [256,128,8192,1024,0,2048,0,1,4,8,0,0,16,2],
  [2048,256,1024,0,128,0,8192,0,16,4,8,2,0,1],
  [2,0,1,0,16,4,8,0,128,0,8192,2048,256,1024],
  [0,2,1,0,8,4,16,0,1024,8192,0,2048,256,128],
  [0,1,0,16,4,8,2,1024,0,128,0,8192,2048,256],
  [0,1,2,4,8,16,0,256,0,1024,2048,0,8192,128],
  [1,0,16,4,8,2,0,256,1024,0,128,0,8192,2048],
  [256,128,0,1024,8192,0,2048,1,0,8,4,16,0,2],
  [1,0,8,4,16,0,2,256,128,0,1024,8192,0,2048],
  [2,1,4,8,0,0,16,128,8192,1024,0,2048,0,256],
  [1,16,4,0,2,8,0,1024,256,2048,128,0,0,8192],
  [256,0,0,2048,1024,128,8192,0,4,2,1,16,8,0],
  [256,1024,0,128,0,8192,2048,1,0,16,4,8,2,0],
  [0,2048,256,128,0,1024,8192,8,4,16,0,2,1,0],
  [1,2,16,8,4,0,0,128,1024,0,256,0,2048,8192],
  [1,2,0,8,0,16,4,128,256,8192,1024,0,2048,0],
  [0,1024,256,0,128,8192,2048,0,0,16,2,8,4,1],
  [0,256,1024,2048,128,8192,0,0,0,4,2,8,16,1],
  [0,0,1,2,4,8,16,0,1024,2048,0,8192,128,256],
  [0,1024,256,0,128,2048,8192,0,4,16,8,2,0,1],
  [1024,256,0,128,2048,8192,0,1,0,4,16,8,2,0],
  [1,0,8,16,4,0,2,1024,128,0,256,8192,2048,0]]

def code (q : List ℕ) (v : V) := q.getD v.val 0
def outside (q : List ℕ) := univ.filter fun v : V => code q v=0
def liftRow (q : List ℕ) (r : ℕ) (v : V) : Bool := (code q v &&& r)!=0

local instance (z : V→Bool) : Decidable (predicate z) := rowDec z

def Good (q : List ℕ) : Prop :=
  (outside q).card=4 ∧ (∀ v : V,code q v∈0::five.signals) ∧
  (∀ r∈five.positives,predicate (liftRow q r)) ∧ (∀ r∈five.negatives,¬predicate (liftRow q r))
instance (q) : Decidable (Good q) := by unfold Good; infer_instance

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem goodEmbedding {q : List ℕ} (h : q∈embeddings) : Good q := by
  have all : embeddings.all (fun q => decide (Good q))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ h)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem coverPair : ∀ x y : V,x≠y → ∃ q∈embeddings,code q x=0 ∧ code q y=0 := by decide +kernel

#print axioms goodEmbedding
#print axioms coverPair
end Checkpoint130.Heawood
