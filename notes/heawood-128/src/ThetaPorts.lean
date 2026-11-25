import ThetaSound
import ThetaData
import Mathlib.Data.List.Sublists

namespace Checkpoint128.Theta
open Checkpoint125

abbrev Slot := {x : ℕ // x∈palette}
def pack (x : ℕ) := palette.getD (masks.idxOf x) 0
def posRow (i : Fin width) := pos.getD (i.val/11) 0
def negRow (i : Fin width) := neg.getD (i.val%11) 0

private theorem paletteFacts : palette.Nodup ∧ (∀ x∈masks,pack x∈palette) ∧
    (∀ i : Fin width,posRow i∈pos ∧ negRow i∈neg) ∧
    ∀ x∈masks, ∀ i : Fin width,
      (pack x).testBit i.val=(x &&& posRow i != 0) ∧
      (pack x).testBit (width+i.val)=(x &&& negRow i != 0) := by
  set_option maxRecDepth 16000 in decide +kernel

theorem packMem {x} (h : x∈masks) : pack x∈palette := paletteFacts.2.1 x h
theorem sampleRows (i : Fin width) : posRow i∈pos ∧ negRow i∈neg := paletteFacts.2.2.1 i
theorem packBits {x} (h : x∈masks) (i : Fin width) :
    (pack x).testBit i.val=(x &&& posRow i != 0) ∧
    (pack x).testBit (width+i.val)=(x &&& negRow i != 0) := paletteFacts.2.2.2 x h i

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootList : (palette.sublists.filter (fun s => coveredBy s==full))=roots := by decide +kernel

/-- A correct circuit on the twelve available signals must start a successful
search from one of the eight possible input sets. -/
theorem rootNecessary {book : List (Binary.Tree Slot)} {e k}
    (bound : book.length≤k) (built : Binary.Built book) (ready : Binary.Ready book e)
    (yes : Correct Subtype.val e) : ∃ s∈roots, search k s=true := by
  let s := palette.attach.filter (fun v => decide (v∈e.vars))
  have sn : s.Nodup := paletteFacts.1.attach.filter _
  have support : s.toFinset=e.vars := by ext v; simp [s]
  have sub : (s.map Subtype.val).Sublist palette := by
    have prior : s.Sublist palette.attach := List.filter_sublist
    have pick := prior.map Subtype.val
    simpa [s] using pick
  have cover := allCovered Subtype.val support.ge yes
  refine ⟨s.map Subtype.val,?_,searchNecessary Subtype.val bound built ready sn support yes⟩
  rw [←rootList]
  exact List.mem_filter.mpr ⟨List.mem_sublists.mpr sub,beq_iff_eq.mpr cover⟩

private def control : List (Bool × ℕ × ℕ) :=
  [(true,4,5),(true,12,6),(false,0,13),(true,5,8),(false,1,15),(true,4,7),
   (true,17,8),(false,2,18),(true,6,7),(false,3,20),(true,14,16),(true,22,19),(true,23,21)]
private def runGate (w : List Bool) (g : Bool × ℕ × ℕ) :=
  let a := w.getD g.2.1 false
  let b := w.getD g.2.2 false
  w++[if g.1 then a || b else a && b]

/-- The explicit thirteen-gate circuit computes the edge predicate on all
512 assignments, with the stated port numbering. -/
theorem controlWorks : control.length=13 ∧
    (∀ p∈control.zipIdx,p.1.2.1<masks.length+p.2 ∧ p.1.2.2<masks.length+p.2) ∧
    ∀ r : Fin 512, (control.foldl runGate (masks.map (fun x => x &&& r.val != 0))).getLast? =
      some (pos.any (fun edge => edge &&& r.val == edge)) := by
  set_option maxRecDepth 30000 in decide +kernel

#print axioms rootNecessary
#print axioms controlWorks
end Checkpoint128.Theta
