import OpeningLift132

namespace Checkpoint132.Completion
open Checkpoint122.Posted

def tail : List (Fin 8192) := [4102,4240,1096,4166,4435,1289,4352,4438,1482,4294,4377,1675,4290,4444,1868,4225,4383,2061,5458,5666,5859,6052,6245,967,6630]

/-- The explicit prescribed-opening circuit attains the posted output with 25 tail gates. -/
theorem control : key 20=284 ∧ tail.length=25 ∧ (codes 20 true true tail).length=27 ∧
    output (codes 20 true true tail)=2097151 := by decide +kernel

def localOps := tail.take 23

theorem localControl : localOps.length=23 ∧
    Checkpoint132.Opening.result Checkpoint132.Opening.localBase (localOps.map Fin.val)=262143 ∧
    (localOps.map Fin.val).all (fun q => decide (q%64≠7 ∧ q/64%64≠7))=true := by decide +kernel

#print axioms control
#print axioms localControl
end Checkpoint132.Completion
