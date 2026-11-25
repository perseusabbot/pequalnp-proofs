import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved15 : List Screen := [
  retarget (block0.getD 6 emptyScreen) ⟨327515,14494,[0,8,2,4,1,0,0,4096,0,0,0,256,8192,128]⟩ [2,5,7,19],
  retarget (block0.getD 4 emptyScreen) ⟨342014,3225,[1,0,0,8,16,0,0,128,0,0,1024,2048,0,0]⟩ [0,11,14,15,20],
  retarget (block0.getD 5 emptyScreen) ⟨343295,11419,[1,2,0,8,16,0,0,128,0,0,1024,2048,0,8192]⟩ [8,9,15,20],
  retarget (block0.getD 5 emptyScreen) ⟨343550,14494,[0,2,1,16,8,0,0,8192,0,0,0,2048,1024,128]⟩ [0,14,15,20],
  retarget (block0.getD 5 emptyScreen) ⟨343806,11419,[8,2,0,1,16,0,0,128,0,0,2048,1024,0,8192]⟩ [0,8,15,20],
  retarget (block0.getD 4 emptyScreen) ⟨343934,3225,[1,0,0,8,16,0,0,128,0,0,1024,2048,0,0]⟩ [0,7,14,15,20],
  retarget (block0.getD 5 emptyScreen) ⟨374747,3545,[128,0,0,1024,2048,0,8192,1,2,0,8,16,0,0]⟩ [2,5,11,19],
  retarget (block0.getD 4 emptyScreen) ⟨374771,3225,[1,0,0,16,8,0,0,1024,0,0,128,2048,0,0]⟩ [2,3,11,14,19]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved15Checked : moved15.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
