import PlaneLookup

namespace Checkpoint133.Plane.Data

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check30 : checkBlock lookup 1920 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check31 : checkBlock lookup 1984 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check32 : checkBlock lookup 2048 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check33 : checkBlock lookup 2112 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check34 : checkBlock lookup 2176 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check35 : checkBlock lookup 2240 64=true := by decide +kernel

end Checkpoint133.Plane.Data
