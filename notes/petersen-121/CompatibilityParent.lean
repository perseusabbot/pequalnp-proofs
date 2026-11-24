import R_meta_1676_118
import L_meta_2010
import L_meta_2014
import PEqualNP.Outside.L_meta_2012
import L_meta_2016

namespace Checkpoint121.Compatibility

/-- Composition of the merged reduction with its four exact child statements. -/
theorem full :
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size :=
  PEqualNP.Outside.R_meta_1676_118 PEqualNP.Outside.L_meta_2010
    PEqualNP.Outside.L_meta_2012 PEqualNP.Outside.L_meta_2014 PEqualNP.Outside.L_meta_2016

#print axioms full
end Checkpoint121.Compatibility
