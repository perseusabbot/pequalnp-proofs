import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved8 : List Screen := [
  retarget (block0.getD 3 emptyScreen) ⟨94143,11419,[1024,128,0,256,8192,0,0,1,0,0,16,4,0,2]⟩ [6,12,15,20],
  retarget (block1.getD 2 emptyScreen) ⟨94175,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [5,12,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨94191,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [4,12,17,18],
  retarget (block1.getD 3 emptyScreen) ⟨94199,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [3,12,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨94203,14494,[0,1,8,4,2,0,0,256,0,0,0,8192,4096,128]⟩ [2,15,18],
  retarget (block0.getD 0 emptyScreen) ⟨95231,9623,[4,1,2,0,8,0,0,256,8192,0,4096,0,0,128]⟩ [10,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨95999,11419,[1,8,0,2,4,0,0,128,0,0,256,8192,0,4096]⟩ [8,11,15,18],
  retarget (block5.getD 4 emptyScreen) ⟨96127,11679,[1,2,16,8,4,0,0,128,1024,0,256,4096,0,8192]⟩ [7,15,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved8Checked : moved8.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
