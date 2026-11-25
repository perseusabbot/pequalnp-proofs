import FloorTests

namespace Checkpoint127.Numbers
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem checked (b : ℕ) (bound : b<256) : segment b=true := by
  interval_cases b <;> decide +kernel

#print axioms checked
end Checkpoint127.Numbers
