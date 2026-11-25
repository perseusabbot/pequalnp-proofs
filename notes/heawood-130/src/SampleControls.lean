import ControlSemantics

namespace Checkpoint130.Upper
open Checkpoint129.Controls

def columns0 : List ℕ := [1,2,4,8,16,32,64,96,128,256]
def edges0 : List ℕ := [17,33,129,18,66,258,36,260,72,136]
def gates0 : List Gate := [(true,4,5),(true,10,8),(false,0,11),(true,4,6),(true,13,9),(false,1,14),(true,5,9),(false,2,16),(true,6,8),(false,3,18),(true,12,15),(true,20,17),(true,21,19)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows0 (b : ℕ) (h : b<16) :
    (List.range 32).all (fun n => decide (correct columns0 edges0 gates0 (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem control114175 : gates0.length=13 ∧
    (∀ p∈gates0.zipIdx,p.1.2.1<columns0.length+p.2 ∧ p.1.2.2<columns0.length+p.2) ∧
    ∀ r : Fin 512, correct columns0 edges0 gates0 r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows0 (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms control114175

def columns1 : List ℕ := [1,2,4,8,16,32,64,128,256,512]
def edges1 : List ℕ := [65,129,34,514,68,260,516,40,264,144]
def gates1 : List Gate := [(true,6,7),(false,0,10),(true,5,9),(false,1,12),(true,6,8),(true,14,9),(false,2,15),(true,5,8),(false,3,17),(false,4,7),(true,11,13),(true,20,16),(true,21,18),(true,22,19)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows1 (b : ℕ) (h : b<32) :
    (List.range 32).all (fun n => decide (correct columns1 edges1 gates1 (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem control114686 : gates1.length=14 ∧
    (∀ p∈gates1.zipIdx,p.1.2.1<columns1.length+p.2 ∧ p.1.2.2<columns1.length+p.2) ∧
    ∀ r : Fin 1024, correct columns1 edges1 gates1 r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows1 (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms control114686

def columns2 : List ℕ := [1,2,4,8,16,32,64,96,128,256]
def edges2 : List ℕ := [17,33,129,18,66,258,36,260,72,136]
def gates2 : List Gate := [(true,4,5),(true,10,8),(false,0,11),(true,4,6),(true,13,9),(false,1,14),(true,5,9),(false,2,16),(true,6,8),(false,3,18),(true,12,15),(true,20,17),(true,21,19)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows2 (b : ℕ) (h : b<16) :
    (List.range 32).all (fun n => decide (correct columns2 edges2 gates2 (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem control126463 : gates2.length=13 ∧
    (∀ p∈gates2.zipIdx,p.1.2.1<columns2.length+p.2 ∧ p.1.2.2<columns2.length+p.2) ∧
    ∀ r : Fin 512, correct columns2 edges2 gates2 r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows2 (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms control126463

def columns3 : List ℕ := [1,2,4,8,16,32,64,128,256,512]
def edges3 : List ℕ := [33,65,129,34,514,68,260,40,264,528]
def gates3 : List Gate := [(true,5,6),(true,10,7),(false,0,11),(true,5,9),(false,1,13),(true,6,8),(false,2,15),(true,5,8),(false,3,17),(false,4,9),(true,12,14),(true,20,16),(true,21,18),(true,22,19)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem rows3 (b : ℕ) (h : b<32) :
    (List.range 32).all (fun n => decide (correct columns3 edges3 gates3 (32*b+n)))=true := by
  interval_cases b <;> decide +kernel

theorem control126719 : gates3.length=14 ∧
    (∀ p∈gates3.zipIdx,p.1.2.1<columns3.length+p.2 ∧ p.1.2.2<columns3.length+p.2) ∧
    ∀ r : Fin 1024, correct columns3 edges3 gates3 r.val := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro r
  have yes := of_decide_eq_true (List.all_eq_true.mp (rows3 (r.val/32) (by omega)) (r.val%32)
    (List.mem_range.mpr (by omega)))
  simpa only [show 32*(r.val/32)+r.val%32=r.val by omega] using yes

#print axioms control126719

end Checkpoint130.Upper
