import ThetaBlocks

namespace Checkpoint128.Theta
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem check_0_4 : block 10 0 4=false := by decide +kernel
theorem check_0_12 : block 10 0 12=false := by decide +kernel
theorem check_0_20 : block 10 0 20=false := by decide +kernel

end Checkpoint128.Theta
