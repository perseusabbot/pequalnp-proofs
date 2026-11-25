import ThetaBlocks

namespace Checkpoint128.Theta
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem check_0_1 : block 10 0 1=false := by decide +kernel
theorem check_0_9 : block 10 0 9=false := by decide +kernel
theorem check_0_17 : block 10 0 17=false := by decide +kernel

end Checkpoint128.Theta
