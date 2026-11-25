import ThetaBlocks

namespace Checkpoint128.Theta
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem check_0_0 : block 10 0 0=false := by decide +kernel
theorem check_0_8 : block 10 0 8=false := by decide +kernel
theorem check_0_16 : block 10 0 16=false := by decide +kernel

end Checkpoint128.Theta
