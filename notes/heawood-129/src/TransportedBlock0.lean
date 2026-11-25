import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved0 : List Screen := [
  retarget (block5.getD 4 emptyScreen) ⟨24575,13727,[1,2,4,8,16,0,0,128,256,0,1024,0,4096,8192]⟩ [13,15,18],
  retarget (block3.getD 0 emptyScreen) ⟨32735,15773,[1,0,4,8,16,0,0,128,256,0,1024,2048,4096,8192]⟩ [5,15,18],
  retarget (block0.getD 0 emptyScreen) ⟨40959,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [13,16,18],
  retarget (block0.getD 0 emptyScreen) ⟨45055,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [12,17,18],
  retarget (block0.getD 3 emptyScreen) ⟨47103,9623,[1,2,4,0,16,0,0,128,256,0,1024,0,0,8192]⟩ [11,14,16,18],
  retarget (block5.getD 0 emptyScreen) ⟨48127,12687,[1,8,4,2,0,0,0,128,256,0,0,0,8192,4096]⟩ [10,14,16,18],
  retarget (block1.getD 3 emptyScreen) ⟨48639,12687,[1,8,4,2,0,0,0,128,256,0,0,0,8192,4096]⟩ [9,14,16,18],
  retarget (block1.getD 0 emptyScreen) ⟨48895,7581,[1,0,4,8,16,0,0,128,256,0,1024,2048,4096,0]⟩ [8,16,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved0Checked : moved0.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
