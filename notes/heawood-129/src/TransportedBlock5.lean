import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved5 : List Screen := [
  retarget (block0.getD 3 emptyScreen) ⟨81855,14494,[0,2,4,1,16,0,0,128,0,0,0,1024,256,8192]⟩ [6,14,15,20],
  retarget (block1.getD 0 emptyScreen) ⟨81887,7581,[1,0,4,8,16,0,0,128,256,0,1024,2048,4096,0]⟩ [5,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨81903,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [4,14,17,18],
  retarget (block1.getD 3 emptyScreen) ⟨81911,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [3,14,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨81915,12687,[2,1,4,8,0,0,0,128,8192,0,0,0,4096,256]⟩ [2,14,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨81917,14494,[0,2,4,1,16,0,0,128,0,0,0,1024,256,8192]⟩ [1,14,15,20],
  retarget (block1.getD 3 emptyScreen) ⟨81918,12687,[2,1,4,8,0,0,0,128,8192,0,0,0,4096,256]⟩ [0,14,15,18],
  retarget (block0.getD 0 emptyScreen) ⟨86015,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [12,15,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved5Checked : moved5.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
