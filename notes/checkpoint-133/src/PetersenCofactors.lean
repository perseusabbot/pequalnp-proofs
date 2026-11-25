import PEqualNP.Outside.L_meta_927
import PEqualNP.MetaComplexity.Helpers.PadOr

namespace Checkpoint133.Petersen
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PadOr

def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def restore (b : Bool) (x : Fin 9 → Bool) : Fin 10 → Bool :=
  ![b, x 6, x 0, x 1, x 7, x 8, x 5, x 2, x 3, x 4]

def cycle (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)

def pad {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin (n+1) → Bool) :=
  x (Fin.last n) || f (fun i => x i.castSucc)

def cycleCircuit : Circuit :=
  ⟨[⟨.or,[1,2]⟩,⟨.and,[0,6]⟩,⟨.or,[1,5]⟩,⟨.and,[3,8]⟩,
    ⟨.or,[2,5]⟩,⟨.and,[4,10]⟩,⟨.or,[7,9]⟩,⟨.or,[11,12]⟩],13⟩

theorem cycleUpper : HasCircuitSize 6 cycle 8 := by
  refine ⟨cycleCircuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, cycleCircuit]
  · decide +kernel

theorem padExact {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (hn : ∃ a b, f a ≠ f b) (upper : HasCircuitSize n f s)
    (lower : ∀ t, HasCircuitSize n f t → s ≤ t) (pos : 0 < s) :
    HasCircuitSize (n+1) (pad f) (s+1) ∧
    ∀ t, HasCircuitSize (n+1) (pad f) t → s+1 ≤ t := by
  refine ⟨pad_up n s f upper, ?_⟩
  intro t h
  cases t with
  | zero =>
    obtain ⟨C, ok, sz, ev⟩ := h
    have h0 := lower 0 (pad_down n 0 f hn ⟨C, ok, by omega, ev⟩)
    omega
  | succ t =>
    exact Nat.succ_le_succ (lower t (pad_down n t f hn h))

set_option maxHeartbeats 0 in
theorem trueShape : (fun x => edge (restore true x)) = pad (pad (pad cycle)) := by
  funext x
  exact (by decide +kernel : ∀ y, edge (restore true y) = pad (pad (pad cycle)) y) x

theorem trueExact : HasCircuitSize 9 (fun x => edge (restore true x)) 11 ∧
    ∀ t, HasCircuitSize 9 (fun x => edge (restore true x)) t → 11 ≤ t := by
  have seven := padExact (f := cycle) ⟨fun _ => false, fun _ => true, by decide⟩
    cycleUpper PEqualNP.Outside.L_meta_927_aux.conj_38 (by decide)
  have eight := padExact (f := pad cycle) ⟨fun _ => false, fun _ => true, by decide⟩
    seven.1 seven.2 (by decide)
  rw [trueShape]
  exact padExact (f := pad (pad cycle)) ⟨fun _ => false, fun _ => true, by decide⟩
    eight.1 eight.2 (by decide)

/-- The first NOT gate becomes a known wire on either cofactor, including on malformed tail indices. -/
theorem splitFirstNot (tail : List Gate) (out : ℕ) (b : Bool) (x : Fin 9 → Bool) :
    (Circuit.mk (⟨.not,[0]⟩::tail) out).eval (List.ofFn (restore b x)) =
      (Circuit.mk tail out).eval (List.ofFn (restore b x) ++ [!b]) := by
  rfl

def remove (y : Fin 10 → Bool) : Fin 9 → Bool :=
  ![y 2, y 3, y 7, y 8, y 9, y 6, y 1, y 4, y 5]

theorem restoreRemove (y : Fin 10 → Bool) : restore (y 0) (remove y) = y := by
  funext i
  fin_cases i <;> rfl

def seeded (b : Bool) (x : Fin 9 → Bool) := List.ofFn (restore b x) ++ [!b]
def rooted (tail : Circuit) : Circuit := ⟨⟨.not,[0]⟩ :: tail.gates,tail.output⟩

/-- One and the same continuation has to compute both nine-input restrictions. -/
theorem commonTail (tail : Circuit) :
    (∀ y, (rooted tail).eval (List.ofFn y) = edge y) ↔
    (∀ x, tail.eval (seeded true x) = pad (pad (pad cycle)) x) ∧
    (∀ x, tail.eval (seeded false x) = edge (restore false x)) := by
  have step (b x) := splitFirstNot tail.gates tail.output b x
  have te (x) := congrFun trueShape x
  constructor
  · intro h
    exact ⟨fun x => (step true x).symm.trans ((h _).trans (te x)),
      fun x => (step false x).symm.trans (h _)⟩
  · rintro ⟨ht,hf⟩ y
    have each (b x) : (rooted tail).eval (List.ofFn (restore b x)) = edge (restore b x) := by
      cases b
      · exact (step false x).trans (hf x)
      · exact (step true x).trans ((ht x).trans (te x).symm)
    simpa only [restoreRemove] using each (y 0) (remove y)

theorem firstNotBudget (tail : Circuit) :
    (FanInTwo (rooted tail) ∧ (rooted tail).size ≤ 19 ∧
      ∀ y, (rooted tail).eval (List.ofFn y) = edge y) ↔
    (FanInTwo tail ∧ tail.size ≤ 18 ∧
      (∀ x, tail.eval (seeded true x) = pad (pad (pad cycle)) x) ∧
      (∀ x, tail.eval (seeded false x) = edge (restore false x))) := by
  have fan : FanInTwo (rooted tail) ↔ FanInTwo tail := by
    simp [FanInTwo,rooted]
  have size : (rooted tail).size ≤ 19 ↔ tail.size ≤ 18 := by
    simp only [rooted,Circuit.size,List.length_cons]
    omega
  rw [fan,size,commonTail]

#print axioms firstNotBudget
#print axioms trueExact
#print axioms splitFirstNot
end Checkpoint133.Petersen
