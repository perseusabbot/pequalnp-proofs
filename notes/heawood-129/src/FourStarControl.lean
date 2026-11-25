import ControlSemantics

namespace Checkpoint129.FourStar
open Checkpoint129.Controls

def columns : List ℕ := [1,2,4,8,16,32,64,128,160,256,320,512,528]
def pairs : List ℕ := [17,33,65,34,258,514,20,132,260,72,136,520]
def gates : List Gate := [(true,4,5),(true,13,6),(false,0,14),(true,5,9),(true,16,11),(false,1,17),(true,4,7),(true,19,9),(false,2,20),(true,6,7),(true,22,11),(false,3,23),(true,15,18),(true,25,21),(true,26,24)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows (b : ℕ) (h : b<32) :
    (List.range 32).all (fun n => decide (correct columns pairs gates (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem controlWorks : gates.length=15 ∧
    (∀ p∈gates.zipIdx,p.1.2.1<columns.length+p.2 ∧ p.1.2.2<columns.length+p.2) ∧
    ∀ r : Fin 1024, correct columns pairs gates r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms controlWorks
end Checkpoint129.FourStar
