import Compression
import LocalData

namespace Checkpoint138

open PEqualNP.Outside.L_meta_9338 Finset

private def scanFour (xs : List Nat) :=
  xs.all fun a => xs.all fun b => xs.all fun c => xs.all fun d => decide (redundant a b c d)

set_option maxHeartbeats 0 in
private theorem masksPass : ∀ t : Fin 3, scanFour (localMasks[t.val]!).toList = true := by
  decide +kernel

private theorem maskMem (t : Fin 3) (i : Fin 18) : mask t i ∈ (localMasks[t.val]!).toList := by
  revert t i
  decide +kernel

private theorem fourMasks (t : Fin 3) (a b c d : Fin 18) :
    redundant (mask t a) (mask t b) (mask t c) (mask t d) := by
  have checked := masksPass t
  simp only [scanFour,List.all_eq_true,decide_eq_true_eq] at checked
  exact checked _ (maskMem t a) _ (maskMem t b) _ (maskMem t c) _ (maskMem t d)

private theorem noLocal (t : Fin 3) : ¬ Pattern 0 (root t) := by
  rintro ⟨ys,hs,inside,through,cross⟩
  have ps (i : Fin 4) : ∃ k : Fin 36, site k = ys i := sitesOK (ys i) (inside i)
  have rs (j : Fin 4) : ∃ k : Fin 18, alt t k = hs j := idsOK t _ (through j)
  choose p hp using ps
  choose r hr using rs
  have entry (i j : Fin 4) : (mask t (r j)).testBit (p i).val = true ↔ i ≠ j := by
    rw [masksOK,hp,hr]
    exact cross i j
  have off (i j : Fin 4) (ne : i ≠ j) := (entry i j).mpr ne
  rcases fourMasks t (r 0) (r 1) (r 2) (r 3) with h|h|h|h
  · exact (entry 3 3).mp (passBit h (off 3 0 (by decide)) (off 3 1 (by decide)) (off 3 2 (by decide))) rfl
  · exact (entry 2 2).mp (passBit h (off 2 0 (by decide)) (off 2 1 (by decide)) (off 2 3 (by decide))) rfl
  · exact (entry 1 1).mp (passBit h (off 1 0 (by decide)) (off 1 2 (by decide)) (off 1 3 (by decide))) rfl
  · exact (entry 0 0).mp (passBit h (off 0 1 (by decide)) (off 0 2 (by decide)) (off 0 3 (by decide))) rfl

theorem noFive : ¬ Crown Inc 5 := by
  rintro ⟨x,h,cross⟩
  let w := firstMoves[(h 0).val]!
  have norm : walk w (h 0) = 0 := startFacts.1 _
  have p : Pattern (h 0) (x 0) := by
    refine ⟨fun i => x i.succ,fun j => h j.succ,?_,?_,?_⟩
    · intro i
      exact (cross i.succ 0).mpr i.succ_ne_zero
    · intro j
      exact (cross 0 j.succ).mpr j.succ_ne_zero.symm
    · intro i j
      exact (cross i.succ j.succ).trans (not_congr Fin.succ_inj)
  let z := moveCells w (x 0)
  have p' : Pattern 0 z := norm ▸ transportPattern w p
  have outside : ¬ Inc z 0 := by
    rw [←norm,walkInc,cross]
    simp
  have zero : bit z.1 z.2 = false := by
    obtain ⟨_,hs,_,hit,_⟩ := p'
    exact zeroOfInc (hit 0)
  obtain ⟨stay,go⟩ := routeOK z zero outside
  have last := transportPattern (route z).2 p'
  rw [stay,go] at last
  exact noLocal _ last

theorem compressCells (S : Finset Cell) :
    ∃ T ⊆ S, T.card ≤ 4 ∧ ∀ h : H, (∀ x ∈ T, Inc x h) ↔ ∀ x ∈ S, Inc x h :=
  fourTests Inc noFive S

theorem compressRectangles (S : Finset H) :
    ∃ T ⊆ S, T.card ≤ 4 ∧ ∀ x : Cell, (∀ h ∈ T, Inc x h) ↔ ∀ h ∈ S, Inc x h :=
  fourTests (fun h x => Inc x h) (fun h => noFive (transposeCrown h)) S

def sharp (i : Fin 4) : Cell := (([2,5,6,7] : List V).getD i.val 0,0)

set_option maxHeartbeats 0 in
theorem sharpFour :
    (∀ h : H, ∃ i : Fin 4, ¬ Inc (sharp i) h) ∧
    (∀ i : Fin 4, ∃ h : H, ∀ j : Fin 4, i ≠ j → Inc (sharp j) h) ∧
    (∀ i : Fin 4, bit (sharp i).1 (sharp i).2 = false) := by decide +kernel

#print axioms noFive
#print axioms compressCells
#print axioms compressRectangles
#print axioms sharpFour

end Checkpoint138
