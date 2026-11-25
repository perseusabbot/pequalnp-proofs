import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved13 : List Screen := [
  retarget (block2.getD 2 emptyScreen) ⟨122239,9623,[1,4,16,0,2,0,0,256,1024,0,128,0,0,8192]⟩ [7,9,13,18],
  retarget (block0.getD 3 emptyScreen) ⟨122591,5549,[1,0,4,2,0,16,0,128,256,0,1024,0,8192,0]⟩ [5,13,17,18],
  retarget (block0.getD 3 emptyScreen) ⟨122719,9907,[128,8192,0,0,1024,256,0,2,0,4,1,0,0,16]⟩ [5,7,13,18],
  retarget (block1.getD 2 emptyScreen) ⟨122799,9623,[128,256,8192,0,4096,0,0,1,2,0,8,0,0,4]⟩ [4,6,13,17],
  retarget (block1.getD 3 emptyScreen) ⟨122861,9623,[128,256,8192,0,4096,0,0,1,2,0,8,0,0,4]⟩ [1,4,13,17],
  retarget (block0.getD 3 emptyScreen) ⟨124671,9907,[2,1,0,0,16,4,0,128,0,256,8192,0,0,1024]⟩ [8,11,12,18],
  retarget (block1.getD 1 emptyScreen) ⟨129967,9907,[1,16,0,0,8,2,0,1024,0,8192,128,0,0,2048]⟩ [4,6,10,17],
  retarget (block0.getD 5 emptyScreen) ⟨310527,11419,[1,2,0,8,16,0,0,128,0,0,1024,2048,0,8192]⟩ [8,9,16,19]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved13Checked : moved13.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
