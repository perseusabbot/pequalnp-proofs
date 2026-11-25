import ProjectedBlock0
import ProjectedBlock1
import ProjectedBlock2
import ProjectedBlock3
import ProjectedBlock4
import ProjectedBlock5
import ProjectedBlock6
import ProjectedBlock7
import ProjectedBlock8
import ProjectedBlock9
import ProjectedBlock10
import ProjectedBlock11
import ProjectedBlock12
import ProjectedBlock13
import ProjectedBlock14
import ProjectedBlock15

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def layers : List Screen := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15

/-- Each directly searched representative satisfies the geometric
and gate-count hypotheses of the projected circuit theorem. -/
theorem allScreensValid {c : Screen} (h : c∈layers) : ValidScreen c := by
  have all : layers.all (fun r => decide (ValidScreen r))=true := by
    simp only [layers,List.all_append,block0Checked,block1Checked,block2Checked,block3Checked,block4Checked,block5Checked,block6Checked,block7Checked,block8Checked,block9Checked,block10Checked,block11Checked,block12Checked,block13Checked,block14Checked,block15Checked,Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp all _ h)

#print axioms allScreensValid
end Checkpoint129.Heawood
