import ThetaTransfer
import ThetaAudit

namespace Checkpoint128.Theta
open Checkpoint125

/-- The kernel-checked eleven-gate search is exhausted on every admissible
input support. This allows all three additional disjunctions as free inputs. -/
theorem localLower {book : List (Binary.Tree Slot)} {e}
    (built : Binary.Built book) (ready : Binary.Ready book e)
    (yes : Correct Subtype.val e) : 12≤book.length := by
  by_contra! short
  obtain ⟨s,hs,hit⟩ := rootNecessary (show book.length≤11 by omega) built ready yes
  rw [closed s hs] at hit
  contradiction
#print axioms localLower
end Checkpoint128.Theta

namespace Checkpoint128.Heawood
open Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood Checkpoint125.Certificate
open Checkpoint127.Heawood PEqualNP.Outside.L_meta_3004_aux.Controls

theorem thetaBudget (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    {p : Shape} (hp : p∈shapes)
    (sub : (interior p.domain).toFinset⊆lost ((run 14 gs).wires.getD out default)) :
    let w := (run 14 gs).wires.getD out default
    (survivors w).card+(endpoints (lost w)).card+w.jobs.card+12≤gs.length+9 := by
  obtain ⟨_,_,ok,ready,yes,cap⟩ := transfer gs out spec hp sub
  have floor := Theta.localLower ok ready yes
  dsimp only at cap ⊢
  omega

theorem elevenLost (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) : 11 ≤ missed ((run 14 gs).wires.getD out default) := by
  let w := (run 14 gs).wires.getD out default
  have ten : 10 ≤ missed w := (Checkpoint127.Heawood.shortCircuits gs out spec).1 short
  change 11 ≤ missed w
  by_contra! low
  obtain ⟨size,h,v,j,listed⟩ := tenProfile gs out spec short (show missed w=10 by omega)
  obtain ⟨p,hp,eq⟩ := shapeOf listed
  have sub : (interior p.domain).toFinset⊆lost w := by
    rw [interiorEq hp,eq,decodeMask]
  have cap := thetaBudget gs out spec hp sub
  change (survivors w).card+(endpoints (lost w)).card+w.jobs.card+12≤gs.length+9 at cap
  change (survivors w).card=11 at h
  change (endpoints (lost w)).card=9 at v
  change w.jobs.card=4 at j
  omega

/-- All 65 posted openings, with each choice of the two opening operations. -/
theorem postedElevenLost (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (wit : Checkpoint122.Posted.Witness i f g tail) :
    let qs := Checkpoint122.Posted.codes i f g tail
    11 ≤ missed ((run 14 (qs.map Checkpoint122.Posted.decode)).wires.getD (13+qs.length) default) := by
  apply elevenLost _ _ (Checkpoint122.Posted.semantics _ wit.2)
  have bound := wit.1
  simp only [List.length_map,Checkpoint122.Posted.codes,List.length_cons]
  omega

#print axioms thetaBudget
#print axioms elevenLost
#print axioms postedElevenLost
end Checkpoint128.Heawood
