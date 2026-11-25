import ThetaBlocks

namespace Checkpoint128.Theta
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem check_0_5 : block 10 0 5=false := by decide +kernel
theorem check_0_13 : block 10 0 13=false := by decide +kernel
theorem check_0_21 : block 10 0 21=false := by decide +kernel

end Checkpoint128.Theta
