import ThetaBlocks

namespace Checkpoint128.Theta
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem check_0_2 : block 10 0 2=false := by decide +kernel
theorem check_0_10 : block 10 0 10=false := by decide +kernel
theorem check_0_18 : block 10 0 18=false := by decide +kernel

end Checkpoint128.Theta
