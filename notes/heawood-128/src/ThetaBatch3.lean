import ThetaBlocks

namespace Checkpoint128.Theta
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem check_0_3 : block 10 0 3=false := by decide +kernel
theorem check_0_11 : block 10 0 11=false := by decide +kernel
theorem check_0_19 : block 10 0 19=false := by decide +kernel

end Checkpoint128.Theta
