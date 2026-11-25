import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16082

def wheel : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [5, 14]⟩, ⟨.and, [7, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_16082

theorem PEqualNP.Outside.L_meta_16082 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 1 && x 6)) 13 := by
  refine ⟨PEqualNP.Outside.L_meta_16082.wheel, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_16082.wheel]
  · decide +kernel
#print axioms PEqualNP.Outside.L_meta_16082
