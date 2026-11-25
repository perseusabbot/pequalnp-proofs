import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved14 : List Screen := [
  retarget (block0.getD 6 emptyScreen) ⟨310751,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [5,9,16,19],
  retarget (block0.getD 5 emptyScreen) ⟨311038,11419,[8,2,0,1,16,0,0,128,0,0,2048,1024,0,8192]⟩ [0,8,16,19],
  retarget (block0.getD 6 emptyScreen) ⟨311262,12687,[8,2,4,1,0,0,0,128,4096,0,0,0,256,8192]⟩ [0,5,16,19],
  retarget (block0.getD 6 emptyScreen) ⟨311286,14494,[0,2,1,4,8,0,0,8192,0,0,0,4096,256,128]⟩ [0,14,16,19],
  retarget (block0.getD 6 emptyScreen) ⟨321503,9623,[4,8,1,0,2,0,0,4096,256,0,8192,0,0,128]⟩ [5,11,12,19],
  retarget (block0.getD 6 emptyScreen) ⟨323423,9159,[256,128,4096,0,0,0,8192,1,4,2,0,0,0,8]⟩ [5,7,12,19],
  retarget (block0.getD 5 emptyScreen) ⟨323447,12687,[1,8,16,2,0,0,0,128,1024,0,0,0,8192,2048]⟩ [3,7,12,19],
  retarget (block0.getD 6 emptyScreen) ⟨327390,11419,[8,2,0,1,4,0,0,128,0,0,4096,256,0,8192]⟩ [0,5,16,19]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved14Checked : moved14.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
