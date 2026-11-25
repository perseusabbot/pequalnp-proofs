import LayerScreens

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def emptyScreen : Screen := ⟨⟨0,0,[]⟩,0,[],[],[],[]⟩

/-- Retain the source test's entire input palette, row specification and cap. -/
def retarget (source : Screen) (shape : Shape) (matching : List (Fin 21)) : Screen :=
  { source with shape := shape, matching := matching }

end Checkpoint129.Heawood
