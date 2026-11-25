import OrbitData
import FloorLogic

namespace Checkpoint127.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Heawood Checkpoint125.Certificate Checkpoint127.Numbers
open PEqualNP.Outside.L_meta_3004_aux.Controls

def decoded (m : ℕ) := univ.filter (fun i : Fin 21 => m.testBit i.val)
theorem decodeMask (L : Finset (Fin 21)) : decoded (edgeMaskOf L)=L := by ext i; simp [decoded,maskBit]
private def relabel (vs : List V) (i : V) := vs.getD i.val 0
def move (f : V→V) (i : Fin 21) := s(f (endpoint i false),f (endpoint i true))
private def Relabels (p : ℕ × List V) : Prop :=
  Function.Bijective (relabel p.2) ∧ (∀ u v : V, G.Adj u v ↔ G.Adj (relabel p.2 u) (relabel p.2 v)) ∧
  (decoded 16071).image (move (relabel p.2))=(decoded p.1).image edge
private instance (p) : Decidable (Relabels p) := by unfold Relabels Function.Bijective Function.Injective Function.Surjective; infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem checks : Ten.relabelings.map Prod.fst=Ten.masks ∧ Ten.relabelings.all (fun p => decide (Relabels p))=true := by decide +kernel

/-- Each listed pattern is the image of mask 16071 under a vertex bijection
preserving Heawood adjacency in both directions. -/
theorem oneOrbit {m} (mem : m∈Ten.masks) :
    ∃ f : V≃V, (∀ u v,G.Adj u v ↔ G.Adj (f u) (f v)) ∧
    (decoded 16071).image (move f)=(decoded m).image edge := by
  rw [←checks.1] at mem
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
  obtain ⟨bij,adj,cover⟩ := of_decide_eq_true (List.all_eq_true.mp checks.2 p hp)
  exact ⟨Equiv.ofBijective _ bij,adj,cover⟩

private def Profile (m : ℕ) := (endpoints (decoded m)).card=9 ∧
  ∃ p∈patches, p.claw=false ∧ p.mask &&& m=p.mask
private instance (m) : Decidable (Profile m) := by unfold Profile; infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem profiles : Ten.masks.all (fun m => decide (Profile m))=true := by decide +kernel

theorem tenGeometry {L : Finset (Fin 21)} (listed : edgeMaskOf L∈Ten.masks) :
    (endpoints L).card=9 ∧ ∃ p∈patches,p.claw=false ∧ (interior p.d).toFinset⊆L := by
  obtain ⟨nine,p,hp,cycle,inside⟩ := of_decide_eq_true (List.all_eq_true.mp profiles _ listed)
  rw [decodeMask] at nine
  refine ⟨nine,p,hp,cycle,?_⟩
  intro i hi
  have bit : p.mask.testBit i.val=true := by
    rw [edgeMask hp,Checkpoint126.Certificate.wordBit]
    exact List.mem_toFinset.mp hi
  have hits := congrArg (fun n : ℕ => n.testBit i.val) inside
  simp only [Nat.testBit_and,bit,Bool.true_and] at hits
  exact (maskBit L i).mp hits

set_option maxRecDepth 12000 in
theorem tenCount : Ten.masks.length=84 ∧ Ten.masks.IsChain (· < ·) := by decide +kernel

#print axioms oneOrbit
#print axioms tenGeometry
#print axioms tenCount
end Checkpoint127.Heawood
