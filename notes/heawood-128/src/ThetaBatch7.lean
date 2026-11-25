import ThetaBlocks

namespace Checkpoint128.Theta
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem check_0_7 : block 10 0 7=false := by decide +kernel
theorem check_0_15 : block 10 0 15=false := by decide +kernel

end Checkpoint128.Theta
