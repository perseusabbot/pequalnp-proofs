import Nine

namespace Checkpoint139

open Finset PEqualNP.Outside.L_meta_9338 Checkpoint138

def tenExample : Finset H := {2,3,7,25,33,77,82,128,132,146}
def nineExample : Finset H := {4,45,69,77,98,117,135,146,162}
def tenWide : Finset H := {0,9,22,33,79,87,100,143,152,167}
def nineWide : Finset H := {19,31,37,73,75,98,145,162,167}
def covered (F : Finset H) := (univ : Finset Cell).filter (fun x => ∃ h ∈ F, Inc x h)

set_option maxHeartbeats 0 in
theorem lightSharp :
    tenExample.card = 10 ∧ (lowRows tenExample).card + (lowCols tenExample).card = 8 ∧
    nineExample.card = 9 ∧ (lowRows nineExample).card + (lowCols nineExample).card = 10 ∧
    (covered nineExample).card = 181 ∧
    nineWide.card = 9 ∧ (lowRows nineWide).card + (lowCols nineWide).card = 11 ∧
    (covered nineWide).card = 215 ∧
    tenWide.card = 10 ∧ (lowRows tenWide).card + (lowCols tenWide).card = 8 ∧
    (covered tenWide).card = 292 := by decide +kernel

#print axioms lightSharp

end Checkpoint139
