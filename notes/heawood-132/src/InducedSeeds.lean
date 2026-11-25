import InducedCertificate
import ThetaSound

namespace Checkpoint132.Induced
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint128.Theta

def signs {t} (σ : Slot t→ℕ) : Prop :=
  ∀ i : Fin width, accepts (fun v => (σ v).testBit i.val) ∧ ¬accepts (fun v => (σ v).testBit (width+i.val))
instance {t} (σ : Slot t→ℕ) : Decidable (signs σ) := by unfold signs; infer_instance

theorem seedFloor {t k : ℕ} (σ : Slot t→ℕ) (s : List (Slot t)) (sign : signs σ)
    (each : ∀ v : Slot t,∃ u,adj v u) (nd : s.Nodup) (all : s.toFinset=univ)
    (closed : search k (s.map σ)=false) : Floor t (k+1) := by
  intro book e built ready ok
  by_contra small
  have inputs : s.toFinset=e.vars := by
    rw [all]
    apply (eq_univ_of_forall _).symm
    intro v
    obtain ⟨u,edge⟩ := each v
    exact used ok edge
  have yes : Correct σ e := fun i =>
    ⟨ok.1 ⟨_,(sign i).1⟩,ok.2 ⟨_,(sign i).2⟩⟩
  have pass := searchNecessary σ (k:=k) (by omega) built ready nd inputs yes
  rw [closed] at pass
  contradiction

#print axioms seedFloor
end Checkpoint132.Induced
