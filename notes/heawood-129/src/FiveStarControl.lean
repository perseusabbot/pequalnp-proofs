import ControlSemantics

namespace Checkpoint129.FiveStar
open Checkpoint129.Controls

def columns : List ℕ := [1,2,4,8,16,32,64,128,256,320,512]
def pairs : List ℕ := [33,65,129,34,514,68,516,40,264,144,272,528]
def gates : List Gate := [(true,5,6),(true,11,7),(false,0,12),(true,5,10),(false,1,14),(true,6,10),(false,2,16),(true,5,8),(false,3,18),(true,7,8),(true,20,10),(false,4,21),(true,13,15),(true,23,17),(true,24,19),(true,25,22)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows (b : ℕ) (h : b<32) :
    (List.range 32).all (fun n => decide (correct columns pairs gates (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem controlWorks : gates.length=16 ∧
    (∀ p∈gates.zipIdx,p.1.2.1<columns.length+p.2 ∧ p.1.2.2<columns.length+p.2) ∧
    ∀ r : Fin 1024, correct columns pairs gates r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms controlWorks
end Checkpoint129.FiveStar
