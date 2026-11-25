import ThetaBlocks

namespace Checkpoint128.Theta
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem check_0_6 : block 10 0 6=false := by decide +kernel
theorem check_0_14 : block 10 0 14=false := by decide +kernel

end Checkpoint128.Theta
