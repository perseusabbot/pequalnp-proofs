import PlaneLookup

namespace Checkpoint133.Plane.Data

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check12 : checkBlock lookup 768 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check13 : checkBlock lookup 832 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check14 : checkBlock lookup 896 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check15 : checkBlock lookup 960 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check16 : checkBlock lookup 1024 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check17 : checkBlock lookup 1088 64=true := by decide +kernel

end Checkpoint133.Plane.Data
