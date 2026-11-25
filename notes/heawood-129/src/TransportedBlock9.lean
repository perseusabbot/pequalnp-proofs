import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved9 : List Screen := [
  retarget (block5.getD 0 emptyScreen) ⟨96191,11419,[1,8,0,2,4,0,0,128,0,0,256,8192,0,4096]⟩ [6,11,15,20],
  retarget (block0.getD 3 emptyScreen) ⟨96223,9623,[1,16,4,0,2,0,0,1024,256,0,128,0,0,8192]⟩ [5,11,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨96247,11419,[2,16,0,4,1,0,0,8192,0,0,128,256,0,1024]⟩ [3,11,15,18],
  retarget (block0.getD 3 emptyScreen) ⟨97023,9623,[1,2,16,0,4,0,0,128,1024,0,256,0,0,8192]⟩ [8,10,15,18],
  retarget (block1.getD 0 emptyScreen) ⟨97215,13471,[256,128,2048,1024,4096,0,0,1,0,0,4,0,16,8]⟩ [6,10,17,19],
  retarget (block0.getD 3 emptyScreen) ⟨97247,9623,[1,16,4,0,2,0,0,1024,256,0,128,0,0,8192]⟩ [5,10,15,18],
  retarget (block5.getD 0 emptyScreen) ⟨97263,9623,[4,2,1,0,8,0,0,8192,256,0,4096,0,0,128]⟩ [4,10,17,18],
  retarget (block1.getD 2 emptyScreen) ⟨97271,13621,[1,0,4,0,8,2,0,0,256,0,128,0,8192,4096]⟩ [3,10,15,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved9Checked : moved9.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
