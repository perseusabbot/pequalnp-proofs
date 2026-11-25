import ControlSemantics

namespace Checkpoint131.Upper
open Checkpoint129.Controls

def columns0 : List ℕ := [1,2,4,8,12,16,32,64,128,256,320,512]
def edges0 : List ℕ := [33,65,129,34,514,68,516,40,264,144,272,528]
def gates0 : List Gate := [(true,6,7),(true,12,8),(false,0,13),(true,6,11),(false,1,15),(true,7,11),(false,2,17),(true,6,9),(false,3,19),(true,8,9),(true,21,11),(false,5,22),(true,14,16),(true,24,18),(true,25,20),(true,26,23)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows0 (b : ℕ) (h : b<32) :
    (List.range 32).all (fun n => decide (correct columns0 edges0 gates0 (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem control128895_11679 : gates0.length=16 ∧
    (∀ p∈gates0.zipIdx,p.1.2.1<columns0.length+p.2 ∧ p.1.2.2<columns0.length+p.2) ∧
    ∀ r : Fin 1024, correct columns0 edges0 gates0 r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows0 (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms control128895_11679

def columns1 : List ℕ := [1,2,4,8,16,32,64,128,256,320,512,640,1024]
def edges1 : List ℕ := [33,65,129,34,1026,68,516,1028,40,264,520,144,272,1040]
def gates1 : List Gate := [(true,5,6),(true,13,7),(false,0,14),(true,5,12),(false,1,16),(true,6,10),(true,18,12),(false,2,19),(true,5,8),(true,21,10),(false,3,22),(true,7,8),(true,24,12),(false,4,25),(true,15,17),(true,27,20),(true,28,23),(true,29,26)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows1 (b : ℕ) (h : b<64) :
    (List.range 32).all (fun n => decide (correct columns1 edges1 gates1 (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem control32767_15775 : gates1.length=18 ∧
    (∀ p∈gates1.zipIdx,p.1.2.1<columns1.length+p.2 ∧ p.1.2.2<columns1.length+p.2) ∧
    ∀ r : Fin 2048, correct columns1 edges1 gates1 r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows1 (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms control32767_15775

def columns2 : List ℕ := [1,2,4,8,12,16,32,36,40,44,64,128,256,384,512,1024,1152,1280,1408,2048]
def edges2 : List ℕ := [65,129,513,66,258,2050,132,2052,72,1032,528,1040,2064,288,544]
def gates2 : List Gate := [(true,10,11),(true,20,14),(false,0,21),(true,10,12),(true,23,19),(false,1,24),(true,11,19),(false,2,26),(true,10,15),(false,3,28),(true,14,15),(true,30,19),(false,5,31),(true,12,14),(false,6,33),(true,22,25),(true,35,27),(true,36,29),(true,37,32),(true,38,34)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows2 (b : ℕ) (h : b<128) :
    (List.range 32).all (fun n => decide (correct columns2 edges2 gates2 (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem control128895_12223 : gates2.length=20 ∧
    (∀ p∈gates2.zipIdx,p.1.2.1<columns2.length+p.2 ∧ p.1.2.2<columns2.length+p.2) ∧
    ∀ r : Fin 4096, correct columns2 edges2 gates2 r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows2 (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms control128895_12223

end Checkpoint131.Upper
