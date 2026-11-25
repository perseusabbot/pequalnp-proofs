import TransportAudit
import FourStarControl
import FiveStarControl

namespace Checkpoint129.Heawood
open Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Heawood
open Checkpoint127.Heawood Checkpoint128.Heawood PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Every listed representative of a short correct circuit must admit a binary
circuit meeting the indicated row tests and gate cap. Transported tables use
exactly the same signal masks, rows and cap as their directly searched source. -/
theorem representativeNecessary (gs : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) {c : Screen} (listed : c∈layers ∨ c∈transported)
    (eq : lost ((run 14 gs).wires.getD out default)=decoded c.shape.mask) :
    ∃ book : List (Binary.Tree {m : ℕ // m∈c.signals}), ∃ t, Binary.Built book ∧ Binary.Ready book t ∧
      book.length≤c.cap ∧
      (∀ n∈c.positives,t.eval (fun m => (m.val &&& n)!=0)) ∧
      (∀ n∈c.negatives,¬t.eval (fun m => (m.val &&& n)!=0)) :=
  projectedScreenNecessary gs out spec short (listed.elim allScreensValid allTransferredValid) eq

/-- The same finite test is necessary for every packed opening in the posted step. -/
theorem postedRepresentativeNecessary (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (wit : Checkpoint122.Posted.Witness i f g tail) {c : Screen}
    (listed : c∈layers ∨ c∈transported)
    (eq : let qs := Checkpoint122.Posted.codes i f g tail
          lost ((run 14 (qs.map Checkpoint122.Posted.decode)).wires.getD (13+qs.length) default)=decoded c.shape.mask) :
    ∃ book : List (Binary.Tree {m : ℕ // m∈c.signals}), ∃ t, Binary.Built book ∧ Binary.Ready book t ∧
      book.length≤c.cap ∧
      (∀ n∈c.positives,t.eval (fun m => (m.val &&& n)!=0)) ∧
      (∀ n∈c.negatives,¬t.eval (fun m => (m.val &&& n)!=0)) := by
  let qs := Checkpoint122.Posted.codes i f g tail
  apply representativeNecessary (qs.map Checkpoint122.Posted.decode) (13+qs.length)
    (Checkpoint122.Posted.semantics _ wit.2) ?_ listed eq
  have bound := wit.1
  simp only [qs,List.length_map,Checkpoint122.Posted.codes,List.length_cons]
  omega

#print axioms representativeNecessary
#print axioms postedRepresentativeNecessary
end Checkpoint129.Heawood
