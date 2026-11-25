import TransportedBlock0
import TransportedBlock1
import TransportedBlock2
import TransportedBlock3
import TransportedBlock4
import TransportedBlock5
import TransportedBlock6
import TransportedBlock7
import TransportedBlock8
import TransportedBlock9
import TransportedBlock10
import TransportedBlock11
import TransportedBlock12
import TransportedBlock13
import TransportedBlock14
import TransportedBlock15
import TransportedBlock16

namespace Checkpoint129.Heawood
open Checkpoint128.Heawood

def transported : List Screen := moved0 ++ moved1 ++ moved2 ++ moved3 ++ moved4 ++ moved5 ++ moved6 ++ moved7 ++ moved8 ++ moved9 ++ moved10 ++ moved11 ++ moved12 ++ moved13 ++ moved14 ++ moved15 ++ moved16

theorem allTransferredValid {c : Screen} (h : c∈transported) : ValidScreen c := by
  have all : transported.all (fun r => decide (ValidScreen r))=true := by
    simp only [transported,List.all_append,moved0Checked,moved1Checked,moved2Checked,moved3Checked,moved4Checked,moved5Checked,moved6Checked,moved7Checked,moved8Checked,moved9Checked,moved10Checked,moved11Checked,moved12Checked,moved13Checked,moved14Checked,moved15Checked,moved16Checked,Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp all _ h)

#print axioms allTransferredValid
end Checkpoint129.Heawood
