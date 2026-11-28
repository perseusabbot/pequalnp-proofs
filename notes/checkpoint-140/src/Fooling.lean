import PEqualNP.Outside.L_meta_9338
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Checkpoint140

open Finset PEqualNP.Outside.L_meta_9338

/-- The chosen zero cells have a one in at least one crossed position of every distinct pair. -/
def Fooling {n : ℕ} (r c : Fin n → V) : Prop :=
  (∀ i, bit (r i) (c i) = false) ∧
  ∀ i j, i ≠ j → bit (r i) (c j) = true ∨ bit (r j) (c i) = true

theorem distinctLabels {n} {r c : Fin n → V} (h : Fooling r c) :
    Function.Injective r ∧ Function.Injective c := by
  constructor <;> intro i j eq <;> by_contra ne
  · rcases h.2 i j ne with a | a
    · rw [eq,h.1 j] at a; contradiction
    · rw [← eq,h.1 i] at a; contradiction
  · rcases h.2 i j ne with a | a
    · rw [← eq,h.1 i] at a; contradiction
    · rw [eq,h.1 j] at a; contradiction

theorem onePerRectangle {n} {r c : Fin n → V} (h : Fooling r c) {b : Box} (ok : legal b)
    {i j : Fin n} (a : hit b (r i) (c i)) (d : hit b (r j) (c j)) : i = j := by
  by_contra ne
  rcases h.2 i j ne with t | t
  · rw [ok _ a.1 _ d.2] at t; contradiction
  · rw [ok _ d.1 _ a.2] at t; contradiction

def inc (p q : V) : ℤ := if bit p q then 1 else 0

private def delta {ι : Type} [DecidableEq ι] (a b : ι) : ℤ := if a=b then 1 else 0

set_option maxHeartbeats 0 in
private theorem planeKernel :
    (∀ p : V, (∑ q : V, inc p q) = 5) ∧
    (∀ p r : V, (∑ q : V, inc p q * inc r q) = 1 + 4*delta p r) := by decide +kernel

def columnDegree {n : ℕ} (r : Fin n → V) (q : V) : ℤ := ∑ i, inc (r i) q

theorem incidenceMoments {n} (r : Fin n → V) (inj : Function.Injective r) :
    (∑ q : V, columnDegree r q) = 5*n ∧
    (∑ q : V, columnDegree r q * columnDegree r q) = (n:ℤ)*n+4*n := by
  constructor
  · unfold columnDegree
    rw [sum_comm]
    simp [planeKernel.1,mul_comm]
  · have expansion (q : V) : columnDegree r q * columnDegree r q =
        ∑ i : Fin n, ∑ j : Fin n, inc (r i) q * inc (r j) q := by
      simp [columnDegree,sum_mul,mul_sum]
      exact sum_comm
    simp_rw [expansion]
    rw [sum_comm]
    have inner (i : Fin n) : (∑ q : V, ∑ j : Fin n, inc (r i) q * inc (r j) q) = n+4 := by
      rw [sum_comm]
      simp [planeKernel.2,delta,inj.eq_iff,sum_add_distrib]
    simp_rw [inner]
    simp; ring

def incidenceTotal {n} (r c : Fin n → V) : ℤ := ∑ j, columnDegree r (c j)

theorem incidenceUpper {n} {r c : Fin n → V} (hr : Function.Injective r) (hc : Function.Injective c) :
    4 * incidenceTotal r c ≤ (n:ℤ)*n + 2*n + 21 := by
  classical
  let L := (univ : Finset (Fin n)).image c
  let d := columnDegree r
  have size : L.card = n := by simp [L,card_image_of_injective _ hc]
  have mass : (∑ q ∈ L, d q) = incidenceTotal r c := by
    unfold incidenceTotal
    exact sum_image (fun i _ j _ h => hc h)
  have cost (q : V) : 4*(if q ∈ L then d q else 0) + 2*d q ≤
      d q * d q + 1 + (if q ∈ L then 8 else 0) := by
    by_cases e : q ∈ L
    · simp only [e,ite_true]; nlinarith [sq_nonneg (d q - 3)]
    · simp only [e,ite_false]; nlinarith [sq_nonneg (d q - 1)]
  have sum := sum_le_sum (s := (univ : Finset V)) (fun q _ => cost q)
  simp only [sum_add_distrib, ← mul_sum] at sum
  have s₁ : (∑ q : V, if q ∈ L then d q else 0) = incidenceTotal r c := by simpa using mass
  have s₂ : (∑ q : V, if q ∈ L then (8:ℤ) else 0) = (n:ℤ)*8 := by simp [size]
  have m := incidenceMoments r hr
  change (∑ q : V, d q) = _ ∧ (∑ q : V, d q*d q) = _ at m
  rw [s₁,s₂,m.1,m.2] at sum
  simp at sum
  linarith

theorem pairLower {n} {r c : Fin n → V} (h : Fooling r c) :
    (n:ℤ)*n ≤ 2*incidenceTotal r c+n := by
  have pair (i j : Fin n) : (1:ℤ) ≤ inc (r i) (c j) + inc (r j) (c i) + delta i j := by
    by_cases e : i=j
    · subst j; simp [inc,h.1,delta]
    · rcases h.2 i j e with a|a <;> simp [inc,a,delta,e] <;> split <;> decide
  have both := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ =>
    sum_le_sum (s := (univ : Finset (Fin n))) (fun j _ => pair i j))
  simp only [sum_add_distrib] at both
  have turn : (∑ i : Fin n, ∑ j : Fin n, inc (r i) (c j)) = incidenceTotal r c := by
    unfold incidenceTotal columnDegree
    rw [sum_comm]
  have back : (∑ i : Fin n, ∑ j : Fin n, inc (r j) (c i)) = incidenceTotal r c := rfl
  rw [turn,back] at both
  simp [delta] at both
  linarith

theorem atMostSeven {n} {r c : Fin n → V} (h : Fooling r c) : n ≤ 7 := by
  have u := incidenceUpper (distinctLabels h).1 (distinctLabels h).2
  have l := pairLower h
  by_contra! more
  have t : (8:ℤ) ≤ n := by exact_mod_cast more
  nlinarith [mul_nonneg (show 0 ≤ (n:ℤ)-8 by omega) (show 0 ≤ (n:ℤ)+4 by omega)]

def sharpRows (i : Fin 7) : V := ([0,1,2,5,6,7,16] : List V).getD i 0
def sharpCols (i : Fin 7) : V := ([1,2,12,6,7,0,5] : List V).getD i 0
theorem sevenAttained : Fooling sharpRows sharpCols := by
  unfold Fooling
  decide +kernel

#print axioms distinctLabels
#print axioms onePerRectangle
#print axioms incidenceMoments
#print axioms incidenceUpper
#print axioms pairLower
#print axioms atMostSeven
#print axioms sevenAttained

end Checkpoint140
