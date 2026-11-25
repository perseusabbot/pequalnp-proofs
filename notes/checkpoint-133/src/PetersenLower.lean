import PetersenCofactors
import PEqualNP.Outside.L_meta_8443

namespace Checkpoint133.Petersen
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.Helpers.Forest PEqualNP.MetaComplexity.Helpers.PermInputs

def deleted (x : Fin 9 → Bool) := edge (restore false x)
def core (x : Fin 8 → Bool) :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) ||
  (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)

/-- The eight vertices in the order of the published thirteen-gate lower bound are
3, 8, 2, 4, 5, 6, 7, 9 in the desk's numbering. Coordinate 6 of the nine-input problem is vertex 1. -/
def coreMap : Fin 9 → Fin 8 := ![2,0,6,1,7,5,0,3,4]
def nineMap : Fin 10 → Fin 9 := ![0,6,0,1,7,8,5,2,3,4]

set_option maxHeartbeats 0 in
theorem coreShape : (fun x => deleted (Function.update (x ∘ coreMap) 6 false)) = core := by
  funext x
  exact (by decide +kernel : ∀ y, deleted (Function.update (y ∘ coreMap) 6 false) = core y) x

theorem nineShape : (fun x => edge (Function.update (x ∘ nineMap) 0 false)) = deleted := by
  funext x
  apply congrArg edge
  funext i
  fin_cases i <;> rfl

theorem falseLower (s : ℕ) (h : HasCircuitSize 9 deleted s) : 14 ≤ s := by
  by_contra! hs
  obtain ⟨C,ok,sz,ev⟩ := h
  have h6 := one_gate_at 8 deleted 6 false 12
    ⟨fun i => decide (i = 0), by decide +kernel⟩
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩ ⟨C,ok,by omega,ev⟩
  have hc := relabel_size coreMap _ 12 h6
  change HasCircuitSize 8 (fun x => deleted (Function.update (x ∘ coreMap) 6 false)) 12 at hc
  rw [coreShape] at hc
  have := PEqualNP.Outside.L_meta_8443 12 hc
  omega

theorem fullLower (s : ℕ) (h : HasCircuitSize 10 edge s) : 15 ≤ s := by
  by_contra! hs
  obtain ⟨C,ok,sz,ev⟩ := h
  have h0 := one_gate_at 9 edge 0 false 13
    ⟨fun i => decide (i = 1), by decide +kernel⟩
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩ ⟨C,ok,by omega,ev⟩
  have hc := relabel_size nineMap _ 13 h0
  change HasCircuitSize 9 (fun x => edge (Function.update (x ∘ nineMap) 0 false)) 13 at hc
  rw [nineShape] at hc
  have := falseLower 13 hc
  omega

def deletedCircuit : Circuit :=
  ⟨[⟨.or,[6,1]⟩, ⟨.or,[9,2]⟩, ⟨.and,[0,10]⟩, ⟨.or,[7,3]⟩,
    ⟨.and,[1,12]⟩, ⟨.or,[7,2]⟩, ⟨.or,[14,5]⟩, ⟨.and,[4,15]⟩,
    ⟨.or,[6,3]⟩, ⟨.and,[5,17]⟩, ⟨.or,[2,3]⟩, ⟨.and,[8,19]⟩,
    ⟨.or,[11,13]⟩, ⟨.or,[21,16]⟩, ⟨.or,[22,18]⟩, ⟨.or,[23,20]⟩],24⟩

set_option maxHeartbeats 0 in
theorem falseUpper : HasCircuitSize 9 deleted 16 := by
  refine ⟨deletedCircuit, ?_, by decide, ?_⟩
  · simp [FanInTwo,deletedCircuit]
  · intro x
    have inputs : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] := rfl
    rw [inputs]
    simp [deletedCircuit,Circuit.eval,Circuit.wires,GateOp.eval,List.getD,deleted,edge,restore,
      Bool.and_or_distrib_left]
    ac_rfl

#print axioms falseUpper
#print axioms falseLower
#print axioms fullLower
end Checkpoint133.Petersen
