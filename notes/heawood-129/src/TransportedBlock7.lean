import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved7 : List Screen := [
  retarget (block1.getD 3 emptyScreen) ⟨90103,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [3,13,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨90107,12687,[2,1,4,8,0,0,0,128,8192,0,0,0,4096,256]⟩ [2,13,15,18],
  retarget (block1.getD 0 emptyScreen) ⟨90109,13471,[256,128,2048,1024,4096,0,0,1,0,0,4,0,16,8]⟩ [1,13,17,19],
  retarget (block0.getD 3 emptyScreen) ⟨92159,11419,[1024,128,0,256,8192,0,0,1,0,0,16,4,0,2]⟩ [11,12,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨93183,12687,[1,8,4,2,0,0,0,128,256,0,0,0,8192,4096]⟩ [10,12,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨93695,12687,[4,2,1,16,0,0,0,8192,256,0,0,0,1024,128]⟩ [9,12,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨93951,14494,[0,2,16,1,4,0,0,128,0,0,0,256,1024,8192]⟩ [8,12,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨94079,11419,[1024,128,0,256,8192,0,0,1,0,0,16,4,0,2]⟩ [7,12,15,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved7Checked : moved7.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
