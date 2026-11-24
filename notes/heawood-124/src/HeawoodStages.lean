import PhysicalStages
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace PEqualNP.Outside.L_meta_3004_aux.Controls
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2268_aux.Normal

set_option maxRecDepth 12000
set_option maxHeartbeats 0

abbrev V := Fin 14
def edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def predicate (x : V → Bool) : Prop :=
  ∃ u v : V, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true

def nbr (v : V) : List V :=
  match v.val with
  | 0 => [7, 8, 10]
  | 1 => [7, 9, 13]
  | 2 => [8, 12, 13]
  | 3 => [7, 11, 12]
  | 4 => [10, 11, 13]
  | 5 => [9, 10, 12]
  | 6 => [8, 9, 11]
  | 7 => [0, 1, 3]
  | 8 => [0, 2, 6]
  | 9 => [1, 5, 6]
  | 10 => [0, 4, 5]
  | 11 => [3, 4, 6]
  | 12 => [2, 3, 5]
  | _ => [1, 2, 4]
private theorem nbr_symm : ∀ u v : V, v ∈ nbr u → u ∈ nbr v := by decide +kernel
private theorem nbr_ne : ∀ v : V, v ∉ nbr v := by decide +kernel

def G : SimpleGraph V where
  Adj u v := v ∈ nbr u
  symm := ⟨fun _ _ h => nbr_symm _ _ h⟩
  loopless := ⟨nbr_ne⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (v ∈ nbr u))

theorem cubic : ∀ v : V, G.degree v = 3 := by decide +kernel

def avoids (root previous current : V) : ℕ → Bool
  | 0 => decide (root ≠ current)
  | k+1 => decide (root ≠ current) && (nbr current).all (fun w =>
    decide (w = previous) || avoids root current w k)

private theorem avoidance : ∀ root : V, (nbr root).all (fun w => avoids root root w 4) = true := by
  decide +kernel

theorem girth_six (root : V) (p : G.Walk root root) (cycle : p.IsCycle) : 6 ≤ p.length := by
  by_contra bad
  have length3 := cycle.three_le_length
  have at1 := (List.all_eq_true.mp (avoidance root)) (p.getVert 1) (by
    have h := p.adj_getVert_succ (show 0 < p.length by omega)
    change p.getVert 1 ∈ nbr (p.getVert 0) at h
    rw [p.getVert_zero] at h
    exact h)
  have advance (i : ℕ) (bound : i+1 ≤ p.length) :
      avoids root (p.getVert i) (p.getVert (i+1)) (4-i) = true := by
    induction i with
    | zero => simpa using at1
    | succ i ih =>
      have old := ih (by omega)
      have fuel : 4-i = (4-(i+1))+1 := by omega
      rw [fuel, avoids, Bool.and_eq_true] at old
      have step := (List.all_eq_true.mp old.2) (p.getVert (i+1+1)) (p.adj_getVert_succ (by omega))
      have diff : p.getVert (i+1+1) ≠ p.getVert i := by
        simpa using (cycle.getVert_sub_one_ne_getVert_add_one (i:=i+1) (by omega)).symm
      simpa [diff] using step
  have last := advance (p.length-1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p.length),p.getVert_length] at last
  cases eqn : 4-(p.length-1) <;> simp [eqn,avoids] at last


theorem adj_orientation : ∀ u v : V, G.Adj u v ↔ (u.val,v.val) ∈ edges ∨ (v.val,u.val) ∈ edges := by
  decide +kernel

theorem orientation (z : V → Bool) : predicate z ↔ ∃ u v : V, G.Adj u v ∧ z u = true ∧ z v = true := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨u,v,(adj_orientation u v).mpr (Or.inl h),hu,hv⟩
  · rintro ⟨u,v,h,hu,hv⟩
    rcases (adj_orientation u v).mp h with uv|vu
    · exact ⟨u,v,uv,hu,hv⟩
    · exact ⟨v,u,vu,hv,hu⟩

/-- Any physical OR–AND–OR circuit computing the posted Heawood edge function
has at least 27 gates, with arbitrary fanout in both OR stages. -/
theorem staged_lower (bot mid top : List Stage.Port) (out : ℕ)
    (valid : ∀ p ∈ mid, p.1 < 14+bot.length ∧ p.2 < 14+bot.length)
    (computes : ∀ z, circuitFun 14 (Stage.circuit 14 bot mid top out) z = true ↔ predicate z) :
    27 ≤ (Stage.circuit 14 bot mid top out).size := by
  exact Stage.physicalLower G ∅ (fun v _ => (G.ncard_neighborSet v).trans (cubic v))
    (by simp) (fun v w h => (by have := girth_six v w h; omega))
    bot mid top out valid (fun z => (computes z).trans (orientation z))

#print axioms staged_lower
end PEqualNP.Outside.L_meta_3004_aux.Controls
