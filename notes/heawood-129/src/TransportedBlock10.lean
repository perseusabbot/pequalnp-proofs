import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved10 : List Screen := [
  retarget (block0.getD 3 emptyScreen) ⟨97535,9623,[1,4,16,0,2,0,0,256,1024,0,128,0,0,8192]⟩ [8,9,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨97759,9623,[1,16,4,0,2,0,0,1024,256,0,128,0,0,8192]⟩ [5,9,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨97775,9623,[4,2,1,0,8,0,0,8192,256,0,4096,0,0,128]⟩ [4,9,17,18],
  retarget (block1.getD 0 emptyScreen) ⟨97783,15645,[4,0,1,16,8,0,0,0,256,0,4096,2048,1024,128]⟩ [3,15,18],
  retarget (block3.getD 0 emptyScreen) ⟨98255,15773,[1,0,4,8,16,0,0,128,256,0,1024,2048,4096,8192]⟩ [4,17,18],
  retarget (block1.getD 0 emptyScreen) ⟨112383,3771,[128,256,0,1024,2048,4096,0,1,0,4,8,16,0,0]⟩ [8,11,18],
  retarget (block0.getD 3 emptyScreen) ⟨112575,11419,[128,1024,0,256,8192,0,0,1,0,0,2,4,0,16]⟩ [6,11,14,19],
  retarget (block1.getD 0 emptyScreen) ⟨112607,3771,[128,256,0,1024,2048,4096,0,1,0,4,8,16,0,0]⟩ [5,11,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved10Checked : moved10.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
