import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved16 : List Screen := [
  retarget (block0.getD 4 emptyScreen) ⟨376059,1699,[1,16,0,0,0,8,0,1024,0,2048,128,0,0,0]⟩ [2,8,9,17,19],
  retarget (block0.getD 6 emptyScreen) ⟨376062,5989,[256,0,4096,0,0,128,8192,0,4,2,1,0,8,0]⟩ [0,8,17,19],
  retarget (block0.getD 4 emptyScreen) ⟨388350,14364,[0,0,1,16,8,0,0,0,0,0,0,2048,1024,128]⟩ [0,8,12,17,19]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved16Checked : moved16.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
