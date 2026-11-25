import ProjectedScreen

namespace Checkpoint129.Controls

abbrev Gate := Bool × ℕ × ℕ

private def step (w : List Bool) (g : Gate) :=
  let a := w.getD g.2.1 false
  let b := w.getD g.2.2 false
  w++[if g.1 then a || b else a && b]

def correct (columns pairs : List ℕ) (gates : List Gate) (r : ℕ) : Prop :=
  (gates.foldl step (columns.map (fun s => s &&& r != 0))).getLast?=
    some (pairs.any (fun e => e &&& r == e))

instance (columns pairs : List ℕ) (gates : List Gate) (r : ℕ) :
    Decidable (correct columns pairs gates r) := by unfold correct; infer_instance

end Checkpoint129.Controls
