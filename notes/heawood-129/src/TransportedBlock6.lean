import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved6 : List Screen := [
  retarget (block5.getD 0 emptyScreen) ⟨88063,9623,[4,1,8,0,2,0,0,256,4096,0,8192,0,0,128]⟩ [11,13,15,18],
  retarget (block5.getD 4 emptyScreen) ⟨89087,13727,[1,2,4,8,16,0,0,128,256,0,1024,0,4096,8192]⟩ [10,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨89599,9623,[4,1,8,0,2,0,0,256,4096,0,8192,0,0,128]⟩ [9,13,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨89855,9623,[1,2,16,0,4,0,0,128,1024,0,256,0,0,8192]⟩ [8,13,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨89983,9623,[128,256,8192,0,4096,0,0,1,2,0,8,0,0,4]⟩ [7,13,15,18],
  retarget (block1.getD 0 emptyScreen) ⟨90047,13471,[256,128,2048,1024,4096,0,0,1,0,0,4,0,16,8]⟩ [6,13,17,19],
  retarget (block1.getD 2 emptyScreen) ⟨90079,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [5,13,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨90095,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [4,13,17,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved6Checked : moved6.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
