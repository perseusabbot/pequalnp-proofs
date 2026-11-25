import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved1 : List Screen := [
  retarget (block0.getD 3 emptyScreen) ⟨49023,9623,[1,2,4,0,16,0,0,128,256,0,1024,0,0,8192]⟩ [7,14,16,18],
  retarget (block0.getD 3 emptyScreen) ⟨49087,14494,[0,2,4,1,16,0,0,128,0,0,0,1024,256,8192]⟩ [6,14,16,19],
  retarget (block1.getD 0 emptyScreen) ⟨49119,7581,[1,0,4,8,16,0,0,128,256,0,1024,2048,4096,0]⟩ [5,16,18],
  retarget (block5.getD 0 emptyScreen) ⟨49135,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [4,14,16,18],
  retarget (block1.getD 3 emptyScreen) ⟨49143,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [3,14,16,18],
  retarget (block5.getD 0 emptyScreen) ⟨49147,12687,[2,1,4,8,0,0,0,128,8192,0,0,0,4096,256]⟩ [2,14,17,18],
  retarget (block0.getD 3 emptyScreen) ⟨49149,14494,[0,2,4,1,16,0,0,128,0,0,0,1024,256,8192]⟩ [1,14,16,19],
  retarget (block1.getD 3 emptyScreen) ⟨49150,12687,[2,1,4,8,0,0,0,128,8192,0,0,0,4096,256]⟩ [0,14,16,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved1Checked : moved1.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
