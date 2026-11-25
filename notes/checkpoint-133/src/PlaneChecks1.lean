import PlaneLookup

namespace Checkpoint133.Plane.Data

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check6 : checkBlock lookup 384 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check7 : checkBlock lookup 448 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check8 : checkBlock lookup 512 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check9 : checkBlock lookup 576 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check10 : checkBlock lookup 640 64=true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check11 : checkBlock lookup 704 64=true := by decide +kernel

end Checkpoint133.Plane.Data
