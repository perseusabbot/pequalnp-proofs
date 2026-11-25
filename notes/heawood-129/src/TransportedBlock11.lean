import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved11 : List Screen := [
  retarget (block0.getD 3 emptyScreen) ⟨112623,11419,[128,1024,0,256,8192,0,0,1,0,0,2,4,0,16]⟩ [4,11,14,18],
  retarget (block14.getD 1 emptyScreen) ⟨112631,3513,[1,0,0,8,16,32,0,128,256,0,1024,2048,0,0]⟩ [3,11,14,18],
  retarget (block14.getD 1 emptyScreen) ⟨112635,9103,[16,1,8,32,0,0,0,1024,2048,256,0,0,0,128]⟩ [2,11,14,18],
  retarget (block2.getD 1 emptyScreen) ⟨112637,11419,[256,128,0,1024,8192,0,0,1,0,0,4,16,0,2]⟩ [1,11,14,19],
  retarget (block14.getD 2 emptyScreen) ⟨112638,3770,[0,2,0,8,16,32,0,128,0,512,1024,2048,0,0]⟩ [0,11,14,18],
  retarget (block0.getD 3 emptyScreen) ⟨113407,5803,[128,256,0,1024,0,8192,0,1,0,4,2,0,16,0]⟩ [8,10,17,18],
  retarget (block0.getD 3 emptyScreen) ⟨113535,9623,[1,2,4,0,16,0,0,128,256,0,1024,0,0,8192]⟩ [7,10,14,18],
  retarget (block2.getD 1 emptyScreen) ⟨114047,9623,[1,4,16,0,2,0,0,256,1024,0,128,0,0,8192]⟩ [7,9,14,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved11Checked : moved11.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
