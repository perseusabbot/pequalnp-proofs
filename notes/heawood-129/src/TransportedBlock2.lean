import TransportData

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def moved2 : List Screen := [
  retarget (block0.getD 0 emptyScreen) ⟨53247,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [12,17,18],
  retarget (block5.getD 0 emptyScreen) ⟨55295,9623,[4,1,8,0,2,0,0,256,4096,0,8192,0,0,128]⟩ [11,13,16,18],
  retarget (block5.getD 4 emptyScreen) ⟨56319,13727,[1,2,4,8,16,0,0,128,256,0,1024,0,4096,8192]⟩ [10,16,18],
  retarget (block1.getD 1 emptyScreen) ⟨57215,12687,[1,8,16,2,0,0,0,128,1024,0,0,0,8192,2048]⟩ [7,13,16,18],
  retarget (block1.getD 0 emptyScreen) ⟨57279,13471,[256,128,2048,1024,4096,0,0,1,0,0,4,0,16,8]⟩ [6,13,16,19],
  retarget (block1.getD 2 emptyScreen) ⟨57311,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [5,13,16,18],
  retarget (block5.getD 0 emptyScreen) ⟨57327,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [4,13,16,18],
  retarget (block1.getD 3 emptyScreen) ⟨57335,12687,[1,2,4,8,0,0,0,128,256,0,0,0,4096,8192]⟩ [3,13,16,18]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem moved2Checked : moved2.all (fun c => decide (ValidScreen c))=true := by decide +kernel

end Checkpoint129.Heawood
