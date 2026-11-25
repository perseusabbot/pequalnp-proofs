import PostedModel

namespace Checkpoint132.Word
open Checkpoint122.Posted

def value (w : List ℕ) (q : ℕ) :=
  if q<4096 then w.getD (q%64) 0 &&& w.getD (q/64%64) 0
  else w.getD (q%64) 0 ||| w.getD (q/64%64) 0

def avoidsCenter (qs : List ℕ) : Prop := ∀ q∈qs,q%64≠7 ∧ q/64%64≠7

def Tracks (R : ℕ→ℕ→Prop) (x y : List ℕ) := x.length=y.length ∧
  ∀ v,v≠7 → R (x.getD v 0) (y.getD v 0)

theorem start {R : ℕ→ℕ→Prop} {x y : List ℕ} (sx : x.length=16) (sy : y.length=16)
    (zero : R 0 0) (small : ∀ v : Fin 16,v.val≠7 → R (x.getD v.val 0) (y.getD v.val 0)) : Tracks R x y := by
  refine ⟨sx.trans sy.symm,fun i ne => ?_⟩
  by_cases h : i<16
  · exact small ⟨i,h⟩ ne
  · simpa only [List.getD_eq_default _ _ (show x.length ≤ i by omega),
      List.getD_eq_default _ _ (show y.length ≤ i by omega)] using zero

theorem propagate {R : ℕ→ℕ→Prop} (zero : R 0 0)
    (meet : ∀ {a b c d},R a c → R b d → R (a &&& b) (c &&& d))
    (join : ∀ {a b c d},R a c → R b d → R (a ||| b) (c ||| d))
    (qs : List ℕ) (safe : avoidsCenter qs) {x y : List ℕ} (track : Tracks R x y) :
    Tracks R (qs.foldl wordStep x) (qs.foldl wordStep y) := by
  induction qs generalizing x y with
  | nil => exact track
  | cons q qs ih =>
    obtain ⟨hl,hr⟩ := safe q (List.mem_cons_self ..)
    apply ih (fun r h => safe r (List.mem_cons_of_mem _ h))
    obtain ⟨len,prior⟩ := track
    have fresh : R (value x q) (value y q) := by
      unfold value
      split
      · exact meet (prior _ hl) (prior _ hr)
      · exact join (prior _ hl) (prior _ hr)
    change Tracks R (x++[value x q]) (y++[value y q])
    refine ⟨by simp [len],fun i ne => ?_⟩
    by_cases early : i<x.length
    · rw [List.getD_append _ _ _ _ early,List.getD_append _ _ _ _ (by omega)]
      exact prior _ ne
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),←len]
      cases i-x.length
      · exact fresh
      · exact zero

def BitLE (i j a b : ℕ) : Prop := a.testBit i=true → b.testBit j=true
instance (i j a b) : Decidable (BitLE i j a b) := by unfold BitLE; infer_instance

theorem bits {i j} (qs : List ℕ) (safe : avoidsCenter qs) {x y : List ℕ} (h : Tracks (BitLE i j) x y) :
    Tracks (BitLE i j) (qs.foldl wordStep x) (qs.foldl wordStep y) := by
  apply propagate (by simp [BitLE]) _ _ qs safe h
  · intro a b c d ac bd yes
    simp only [Nat.testBit_and,Bool.and_eq_true] at yes ⊢
    exact ⟨ac yes.1,bd yes.2⟩
  · intro a b c d ac bd yes
    simp only [Nat.testBit_or,Bool.or_eq_true] at yes ⊢
    exact yes.imp ac bd

theorem sizes (qs : List ℕ) (w : List ℕ) : (qs.foldl wordStep w).length=w.length+qs.length := by
  induction qs generalizing w with
  | nil => simp
  | cons q qs ih => simp only [List.foldl_cons,ih,wordStep,List.length_append,List.length_cons,List.length_nil]; omega

theorem unchanged (qs : List ℕ) (w : List ℕ) (i : ℕ) (early : i<w.length) :
    (qs.foldl wordStep w).getD i 0=w.getD i 0 := by
  induction qs generalizing w with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rw [ih (wordStep w q) (by simp only [wordStep,List.length_append,List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ early

#print axioms bits
#print axioms sizes
#print axioms unchanged
end Checkpoint132.Word
