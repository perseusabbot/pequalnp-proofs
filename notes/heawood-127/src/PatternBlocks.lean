import EightPatterns
import BoundaryData

namespace Checkpoint125.Heawood.PatternProof
open PEqualNP.Outside.L_meta_3004_aux.Controls

def centerSets := (List.finRange 14).sublistsLen 5
def part (b : ℕ) := ((centerSets.drop (32*b)).take 32)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem chunks : ((List.range 63).map part).flatten=centerSets := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked (b : ℕ) (bound : b<63) :
    (part b).flatMap fromCenters=BoundaryData.blocks.getD b [] := by
  interval_cases b <;> decide +kernel

end Checkpoint125.Heawood.PatternProof
