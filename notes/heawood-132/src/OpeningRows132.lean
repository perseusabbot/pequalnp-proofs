import WordTransport132

namespace Checkpoint132.Opening
open Checkpoint122.Posted Checkpoint132.Word
open PEqualNP.Outside.L_meta_3008_aux (nums)

def base := ((codes 20 true true []).foldl wordStep nums)
def overlay := base.getD 7 0 &&& base.getD 15 0
def localBase : List ℕ := [187639692001346,224517431525392,150096457043972,264724335830016,212188564424832,280375465099552,176068437213705,0,93821685989383,881912447032,16018833856,16492931583488,257731358720,56076976226304,262486086418514,280358250652754]
def posLink : List ℕ := [0,1,6,0,4,15,2,12,16,0,10,13,7,11,17,5,8,14,0,3,9]
def negLink : List ℕ := [47,47,46,46,39,39,38,33,33,31,32,43,43,42,26,27,25,37,37,36,35,34,23,24,22,45,45,44,30,29,28,41,40,21,19,20,18]

theorem dimensions : base.length=16 ∧ localBase.length=16 ∧ overlay<2^58 := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem positiveLinks : ∀ i : Fin 21,overlay.testBit i.val=true ∨
    (posLink.getD i.val 0<18 ∧ ∀ v : Fin 16,v.val≠7 →
     BitLE (posLink.getD i.val 0) i.val (localBase.getD v.val 0) (base.getD v.val 0)) := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem negativeLinks : ∀ j : Fin 37,overlay.testBit (21+j.val)=false ∧
    18≤negLink.getD j.val 0 ∧ ∀ v : Fin 16,v.val≠7 →
    BitLE (21+j.val) (negLink.getD j.val 0) (base.getD v.val 0) (localBase.getD v.val 0) := by decide +kernel

theorem boundedBase : ∀ v : Fin 16,base.getD v.val 0<2^58 := by decide +kernel

#print axioms dimensions
#print axioms positiveLinks
#print axioms negativeLinks
#print axioms boundedBase
end Checkpoint132.Opening
