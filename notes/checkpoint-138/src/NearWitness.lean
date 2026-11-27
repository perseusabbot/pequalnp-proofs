import Board

namespace Checkpoint138

open PEqualNP.Outside.L_meta_9338

def nearId (i : Fin 15) : H :=
  ([6,30,35,39,57,59,67,87,96,108,134,138,141,154,164] : List H).getD i.val 0

set_option maxHeartbeats 0 in
theorem nearWitness :
    (∀ a b : Fin 15, nearId a = nearId b → a = b) ∧
    (∀ x : Cell, bit x.1 x.2 = false →
      ((¬ ∃ a : Fin 15, Inc x (nearId a)) ↔ x = (8,16) ∨ x = (10,16))) ∧
    (bit 8 16 = false ∧ bit 10 16 = false) ∧
    ((Finset.univ : Finset Cell).filter (fun x => ∃ a : Fin 15, Inc x (nearId a))).card = 334 := by
  decide +kernel

#print axioms nearWitness

end Checkpoint138
