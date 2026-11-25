import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved3 : List Screen := [
  retarget (block5.getD 0 emptyScreen) ⟨57339,12687,[2,1,4,8,0,0,0,128,8192,0,0,0,4096,256]⟩ [2,13,17,18],
  retarget (block1.getD 0 emptyScreen) ⟨57341,13471,[256,128,2048,1024,4096,0,0,1,0,0,4,0,16,8]⟩ [1,13,16,19],
  retarget (block1.getD 0 emptyScreen) ⟨59391,10655,[256,128,4096,1024,2048,0,0,1,4,0,0,16,0,8]⟩ [11,12,18],
  retarget (block1.getD 0 emptyScreen) ⟨61311,10655,[256,128,4096,1024,2048,0,0,1,4,0,0,16,0,8]⟩ [7,12,18],
  retarget (block1.getD 2 emptyScreen) ⟨61407,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [5,12,17,18],
  retarget (block5.getD 0 emptyScreen) ⟨61423,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [4,12,17,18],
  retarget (block1.getD 3 emptyScreen) ⟨61431,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [3,12,17,18],
  retarget (block5.getD 4 emptyScreen) ⟨61435,14751,[16,2,1,4,8,0,0,8192,1024,0,0,4096,256,128]⟩ [2,17,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved3Checked : moved3.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
