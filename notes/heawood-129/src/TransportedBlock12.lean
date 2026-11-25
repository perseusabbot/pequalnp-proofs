import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved12 : List Screen := [
  retarget (block14.getD 2 emptyScreen) ⟨114167,10023,[32,8,2,0,0,16,0,0,512,2048,1024,0,0,128]⟩ [3,14,17,18],
  retarget (block14.getD 1 emptyScreen) ⟨114427,6543,[16,32,8,1,0,0,0,1024,2048,0,0,256,128,0]⟩ [2,8,17,18],
  retarget (block2.getD 1 emptyScreen) ⟨114429,5803,[256,1024,0,128,0,8192,0,1,0,16,4,0,2,0]⟩ [1,8,17,19],
  retarget (block0.getD 3 emptyScreen) ⟨120575,9623,[1,2,16,0,4,0,0,128,1024,0,256,0,0,8192]⟩ [8,11,13,18],
  retarget (block5.getD 0 emptyScreen) ⟨120767,9907,[256,128,0,0,4096,8192,0,1,0,2,4,0,0,8]⟩ [6,11,13,19],
  retarget (block5.getD 0 emptyScreen) ⟨120815,9623,[128,256,8192,0,4096,0,0,1,2,0,8,0,0,4]⟩ [4,11,13,18],
  retarget (block2.getD 1 emptyScreen) ⟨120823,9907,[128,8192,0,0,256,1024,0,2,0,16,1,0,0,4]⟩ [3,11,13,18],
  retarget (block5.getD 0 emptyScreen) ⟨120829,9907,[256,128,0,0,4096,8192,0,1,0,2,4,0,0,8]⟩ [1,11,13,19]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved12Checked : moved12.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
