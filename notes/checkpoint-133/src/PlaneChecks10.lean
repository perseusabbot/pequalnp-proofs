import PlaneLookup

namespace Checkpoint133.Plane.Data

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check60 : checkBlock lookup 3840 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check61 : checkBlock lookup 3904 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check62 : checkBlock lookup 3968 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check63 : checkBlock lookup 4032 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check64 : checkBlock lookup 4096 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check65 : checkBlock lookup 4160 64=true := by decide +kernel

end Checkpoint133.Plane.Data
