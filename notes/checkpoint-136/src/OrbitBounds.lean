import Mathlib.GroupTheory.Sylow
import OrbitDivisibility

namespace Checkpoint136
open MulAction

private theorem smallStabilizer {Q T : Type*} [Group Q] [Finite Q] [MulAction Q T]
    (size : Nat.card Q=256) (t : T) (k d : ℕ)
    (excluded : ∀H : Subgroup Q,Nat.card H=2^k → ¬H≤stabilizer Q t)
    (divisors : ∀x : Fin (2^k),x.val∣256 → x.val∣d) : Nat.card (stabilizer Q t)∣d := by
  have power : IsPGroup 2 Q := IsPGroup.of_card (n:=8) (by simpa using size)
  have small : Nat.card (stabilizer Q t)<2^k := by
    by_contra! h
    obtain ⟨H,sub,card⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card (n:=k)
      Nat.prime_two power h
    exact excluded H card sub
  have divisor := (stabilizer Q t).card_subgroup_dvd_card
  rw [size] at divisor
  exact divisors ⟨_,small⟩ divisor

theorem stabilizerFour {Q T : Type*} [Group Q] [Finite Q] [MulAction Q T]
    (size : Nat.card Q=256) (t : T)
    (excluded : ∀H : Subgroup Q,Nat.card H=8 → ¬H≤stabilizer Q t) :
    Nat.card (stabilizer Q t) ∣ 4 := smallStabilizer size t 3 4 excluded (by decide)

/-- The order-eight search and the odd divisors from Checkpoint 135 combine
for a full collection of labeled images. -/
theorem sixtyFourImages {Q T : Type*} [Group Q] [Finite Q] [MulAction Q T] [Finite T]
    (size : Nat.card Q=256)
    (excluded : ∀t : T,∀H : Subgroup Q,Nat.card H=8 → ¬H≤stabilizer Q t) :
    64 ∣ Nat.card T := by
  exact Checkpoint135.OrbitDivisibility.orbitMultiplier 64 4 size
    (fun t => stabilizerFour size t (excluded t))

theorem smallImageCount (n : ℕ) (even : 64∣n) (odd : 945∣n) : 60480∣n :=
  (by decide : Nat.Coprime 64 945).mul_dvd_of_dvd_of_dvd even odd

theorem fifteenImageCount (n : ℕ) (even : 64∣n) (odd : 315∣n) : 20160∣n :=
  (by decide : Nat.Coprime 64 315).mul_dvd_of_dvd_of_dvd even odd

/-- Excluding the order-four subgroups supplies a further factor of two. -/
theorem oneTwentyEightImages {Q T : Type*} [Group Q] [Finite Q] [MulAction Q T] [Finite T]
    (size : Nat.card Q=256)
    (excluded : ∀t : T,∀H : Subgroup Q,Nat.card H=4 → ¬H≤stabilizer Q t) :
    128 ∣ Nat.card T :=
  Checkpoint135.OrbitDivisibility.orbitMultiplier 128 2 size
    (fun t => smallStabilizer size t 2 2 (excluded t) (by decide))

theorem smallerImageCount (n : ℕ) (even : 128∣n) (odd : 945∣n) : 120960∣n :=
  (by decide : Nat.Coprime 128 945).mul_dvd_of_dvd_of_dvd even odd

#print axioms oneTwentyEightImages
#print axioms smallerImageCount
#print axioms stabilizerFour
#print axioms sixtyFourImages
#print axioms smallImageCount
#print axioms fifteenImageCount
end Checkpoint136
