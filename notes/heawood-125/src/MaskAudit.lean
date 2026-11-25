import MatchingTable

namespace Checkpoint125.Certificate

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem verified (b : ℕ) (bound : b<128) : block b=true := by
  interval_cases b <;> decide +kernel

/-- Check each possible omitted edge count against a concrete matching for
each of the 16,384 endpoint sets. The finite check uses kernel reduction. -/
theorem numerical {d m : ℕ} (bound : d<16384) (capacity : m≤(interior d).length)
    (ends : (vertexList d).length≤2*m) :
    floor m+1 ≤ 21-m + max ((21-m+2)/3) (retained d).length + (vertexList d).length +
      (if 3*(vertexList d).length<4*m then 1 else 0) := by
  have h := List.all_eq_true.mp (verified (d/128) (by omega)) (d%128) (List.mem_range.mpr (by omega))
  change checkMask (128*(d/128)+d%128)=true at h
  rw [show 128*(d/128)+d%128=d by omega] at h
  exact of_decide_eq_true (List.all_eq_true.mp h m (List.mem_range.mpr (by omega))) ends

#print axioms numerical
end Checkpoint125.Certificate
