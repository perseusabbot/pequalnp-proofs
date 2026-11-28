import ColorCover

namespace Checkpoint140

open Finset

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def load (U B : Finset α) (w : α → ℕ) := ∑ x ∈ U, if x ∈ B then w x else 0

omit [DecidableEq β] in
theorem totalLoad {U : Finset α} {F : Finset β} {B : β → Finset α} (w : α → ℕ)
    (cover : ∀ x ∈ U, ∃ b ∈ F, x ∈ B b) :
    (∑ x ∈ U, w x) ≤ ∑ b ∈ F, load U (B b) w := by
  calc
    _ ≤ ∑ x ∈ U, ∑ b ∈ F, if x ∈ B b then w x else 0 := by
      apply sum_le_sum
      intro x hx
      obtain ⟨b,hb,inB⟩ := cover x hx
      have h := single_le_sum (s := F) (f := fun j => if x ∈ B j then w x else 0)
        (fun j _ => Nat.zero_le _) hb
      simpa [inB] using h
    _ = _ := sum_comm

omit [DecidableEq β] in
theorem heavyMember {U : Finset α} {F : Finset β} {B : β → Finset α} (w : α → ℕ)
    (nonempty : F.Nonempty) (cap : F.card ≤ m) (cover : ∀ x ∈ U, ∃ b ∈ F, x ∈ B b) :
    ∃ b ∈ F, (∑ x ∈ U,w x) ≤ m * load U (B b) w ∧ ∀ j ∈ F, load U (B j) w ≤ load U (B b) w := by
  obtain ⟨b,hb,largest⟩ := exists_max_image F (fun j => load U (B j) w) nonempty
  refine ⟨b,hb,?_,largest⟩
  calc
    _ ≤ ∑ j ∈ F, load U (B j) w := totalLoad w cover
    _ ≤ ∑ _j ∈ F, load U (B b) w := sum_le_sum largest
    _ ≤ m * load U (B b) w := by simpa using Nat.mul_le_mul_right (load U (B b) w) cap

theorem memberFloor {U : Finset α} {F : Finset β} {B : β → Finset α} (w : α → ℕ)
    (cover : ∀ x ∈ U, ∃ b ∈ F, x ∈ B b) (budget : F.card ≤ m)
    (bound : ∀ j ∈ F, load U (B j) w ≤ M) {b : β} (hb : b ∈ F) :
    (∑ x ∈ U,w x) ≤ load U (B b) w + (m-1)*M := by
  have rest : (∑ j ∈ F.erase b, load U (B j) w) ≤ (F.card-1)*M := by
    calc
      _ ≤ ∑ _j ∈ F.erase b, M := sum_le_sum (fun j hj => bound j (mem_of_mem_erase hj))
      _ = _ := by simp [card_erase_of_mem hb]
  have small : (F.card-1)*M ≤ (m-1)*M := Nat.mul_le_mul_right M (Nat.sub_le_sub_right budget 1)
  calc
    _ ≤ ∑ j ∈ F, load U (B j) w := totalLoad w cover
    _ = (∑ j ∈ F.erase b, load U (B j) w) + load U (B b) w := (sum_erase_add F _ hb).symm
    _ ≤ (m-1)*M + load U (B b) w := Nat.add_le_add_right (rest.trans small) _
    _ = _ := Nat.add_comm _ _

#print axioms totalLoad
#print axioms heavyMember
#print axioms memberFloor

end Checkpoint140
