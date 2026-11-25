import PlaneMinimum
import Mathlib.Data.Fintype.Prod

namespace Checkpoint133.Plane
open Finset

abbrev Words := ℕ × ℕ
def inWords (w : Words) (i j : V) := w.1.testBit i.val && w.2.testBit j.val
def inFamily (ws : List Words) (i j : V) := ws.any (fun w => inWords w i j)
def unpack (w : Words) : Box :=
  (univ.filter (fun i : V => w.1.testBit i.val), univ.filter (fun j : V => w.2.testBit j.val))

theorem inUnpacked (ws : List Words) (i j : V) :
    inFamily ws i j = true ↔ ∃ b ∈ ws.map unpack, i ∈ b.1 ∧ j ∈ b.2 := by
  simp [inFamily,inWords,unpack]

def nearWords : List Words := [(295235,595464), (100490,664112), (141361,573764), (1053333,304128), (290840,98530), (75401,526354), (1058880,180491), (543504,1183814), (787620,1124609), (114692,393592), (1065122,166404), (1087008,270477), (725058,1066640), (1180940,284705)]
def nearMissing : List (V × V) := [(6,18), (13,10)]

theorem nearCells : ∀ i j : V, inFamily nearWords i j = true ↔ zeroCell i j ∧ (i,j) ∉ nearMissing := by
  intro i
  fin_cases i <;> decide +kernel

theorem nearLengths : nearWords.length = 14 ∧ nearMissing.toFinset.card = 2 := by decide +kernel

def symWords : List Words := [(1537,800798), (12296,114931), (98368,919448), (786944,1064131), (4099,124444), (32792,995552), (262336,1672963), (141361,573764), (1130888,395810), (658500,1069329), (1073698,166028), (200980,1328224), (1607840,140037), (279814,1120296)]
def symMissing : List (V × V) := [(1,19), (2,13), (2,15), (2,17), (4,1), (5,16), (5,18), (5,20), (7,4), (8,0), (8,2), (8,19), (10,7), (11,1), (11,3), (11,5), (13,10), (14,4), (14,6), (14,8), (16,13), (17,7), (17,9), (17,11), (19,16), (20,10), (20,12), (20,14)]

theorem symCells : ∀ i j : V, inFamily symWords i j = true ↔ zeroCell i j ∧ (i,j) ∉ symMissing := by
  intro i
  fin_cases i <;> decide +kernel

theorem symLengths : symWords.length = 14 ∧ symMissing.toFinset.card = 28 := by decide +kernel

theorem validOfCells {ws : List Words} {miss : List (V × V)}
    (h : ∀ i j, inFamily ws i j = true ↔ zeroCell i j ∧ (i,j) ∉ miss) :
    ∀ b ∈ ws.map unpack, Good b := by
  intro b hb i hi j hj
  exact ((h i j).mp ((inUnpacked ws i j).mpr ⟨b,hb,hi,hj⟩)).1

theorem nearCover : (nearWords.map unpack).length = 14 ∧
    (∀ b ∈ nearWords.map unpack,Good b) ∧
    ∀ i j : V, (∃ b ∈ nearWords.map unpack, i ∈ b.1 ∧ j ∈ b.2) ↔
      (lines.getD i.val 0).testBit j.val = false ∧ (i,j) ∉ nearMissing := by
  refine ⟨by decide,validOfCells nearCells,?_⟩
  intro i j
  rw [←inUnpacked,nearCells,onDeskBoard]

-- Count the required entries of the posted matrix directly from the row words.
set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem requiredCard : ((univ : Finset (V × V)).filter (fun p => zeroCell p.1 p.2)).card = 336 := by
  decide +kernel

def countHits (ws : List Words) := ((List.finRange 21).map
  (fun i => ((List.finRange 21).filter (fun j => inFamily ws i j)).length)).sum

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem achieved : countHits nearWords = 334 ∧ countHits symWords = 308 := by decide +kernel

#print axioms achieved
#print axioms nearCover
#print axioms symCells
#print axioms requiredCard
end Checkpoint133.Plane
