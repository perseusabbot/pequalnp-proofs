import PlaneLookup

namespace Checkpoint133.Plane.Data

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check24 : checkBlock lookup 1536 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check25 : checkBlock lookup 1600 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check26 : checkBlock lookup 1664 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check27 : checkBlock lookup 1728 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check28 : checkBlock lookup 1792 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check29 : checkBlock lookup 1856 64=true := by decide +kernel

end Checkpoint133.Plane.Data
