import ProgramFloor

namespace Checkpoint131.Full
open Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Heawood
open Checkpoint130.Cut Checkpoint130.Heawood PEqualNP.Outside.L_meta_3004_aux.Controls

def positives : List ℕ := [129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112]
def negatives : List ℕ := [127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
def row (r : ℕ) (v : V) : Bool := r.testBit v.val

theorem rowSigns :
    (∀ r∈positives, edgeOn (row r)=true) ∧ (∀ r∈negatives, edgeOn (row r)=false) := by
  decide +kernel

def signature (v : V) : ℕ :=
  ((positives++negatives).zipIdx.map fun ⟨r,i⟩ => if row r v then 2^i else 0).sum

theorem inputColumns : (List.ofFn signature) = [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] := by decide +kernel

def Holds (e : Binary.Tree V) : Prop :=
  (∀ r∈positives,e.eval (fun v => row r v=true)) ∧ ∀ r∈negatives,¬e.eval (fun v => row r v=true)

theorem programFromRows (k : ℕ)
    (floor : ∀ gs : List (Binary.Tree V), ∀ e, Binary.Built gs → Binary.Ready gs e → Holds e → k≤gs.length)
    (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) : k≤ops.length := by
  obtain ⟨gs,e,hb,hr,hc,truth⟩ := vertexProgram ops out spec
  apply Nat.le_trans (floor gs e hb hr ?_) hc
  exact ⟨fun r h => (truth (row r)).mpr ((edgeOnCorrect _).mp (rowSigns.1 r h)),
    fun r h accepted => Bool.false_ne_true ((rowSigns.2 r h).symm.trans
      ((edgeOnCorrect _).mpr ((truth (row r)).mp accepted)))⟩

theorem postedTwentyFour
    (floor : ∀ gs : List (Binary.Tree V), ∀ e, Binary.Built gs → Binary.Ready gs e → Holds e → 24≤gs.length)
    (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (h : Checkpoint122.Posted.Witness i f g tail) : 22≤tail.length := by
  let qs := Checkpoint122.Posted.codes i f g tail
  have size := programFromRows 24 floor (qs.map Checkpoint122.Posted.decode) (13+qs.length)
    (Checkpoint122.Posted.semantics _ h.2)
  simp only [List.length_map,qs,Checkpoint122.Posted.codes,List.length_cons] at size
  omega

#print axioms rowSigns
#print axioms inputColumns
#print axioms programFromRows
#print axioms postedTwentyFour
end Checkpoint131.Full
