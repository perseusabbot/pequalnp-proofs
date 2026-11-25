import SeedRanks1
import InducedProgram

namespace Checkpoint132.Induced
open Checkpoint122.Pruning Checkpoint124.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

theorem programTwentyOne (checks : SeedChecks) (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) : 21≤ops.length :=
  programOfInducedFloor (seed16383 checks) ops out spec

theorem postedTwentyOne (checks : SeedChecks) (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (h : Checkpoint122.Posted.Witness i f g tail) : 19≤tail.length := by
  let qs := Checkpoint122.Posted.codes i f g tail
  have bound := programTwentyOne checks (qs.map Checkpoint122.Posted.decode) (13+qs.length)
    (Checkpoint122.Posted.semantics _ h.2)
  simp only [List.length_map,qs,Checkpoint122.Posted.codes,List.length_cons] at bound
  omega

#print axioms programTwentyOne
#print axioms postedTwentyOne
end Checkpoint132.Induced
