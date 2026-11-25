import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved4 : List Screen := [
  retarget (block1.getD 0 emptyScreen) ⟨65487,7581,[1,0,4,8,16,0,0,128,256,0,1024,2048,4096,0]⟩ [4,16,18],
  retarget (block3.getD 0 emptyScreen) ⟨65495,15773,[1,0,4,8,16,0,0,128,256,0,1024,2048,4096,8192]⟩ [3,16,18],
  retarget (block0.getD 0 emptyScreen) ⟨73727,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [13,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨79871,9623,[1,2,4,0,16,0,0,128,256,0,1024,0,0,8192]⟩ [11,14,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨80895,12687,[1,8,4,2,0,0,0,128,256,0,0,0,8192,4096]⟩ [10,14,15,18],
  retarget (block1.getD 3 emptyScreen) ⟨81407,12687,[1,8,4,2,0,0,0,128,256,0,0,0,8192,4096]⟩ [9,14,15,18],
  retarget (block1.getD 0 emptyScreen) ⟨81663,7581,[1,0,4,8,16,0,0,128,256,0,1024,2048,4096,0]⟩ [8,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨81791,9623,[1,2,4,0,16,0,0,128,256,0,1024,0,0,8192]⟩ [7,14,15,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved4Checked : moved4.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
