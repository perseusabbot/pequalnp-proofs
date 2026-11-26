import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace Checkpoint135.OrbitDivisibility
open MulAction

private theorem cardProduct {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Nat.card (orbit G x) * Nat.card (stabilizer G x)=Nat.card G := by
  rw [←Nat.card_prod]
  exact Nat.card_congr (orbitProdStabilizerEquivGroup G x)

private theorem primeAbsent {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (x : X) {p : ℕ} (prime : p.Prime) (away : ∀g : G,orderOf g=p → g • x≠x) :
    ¬p ∣ Nat.card (stabilizer G x) := by
  intro divides
  let _ : Fact p.Prime := ⟨prime⟩
  obtain ⟨g,h⟩ := exists_prime_orderOf_dvd_card' p divides
  exact away g ((Subgroup.orderOf_coe g).trans h) (mem_stabilizer_iff.mp g.property)

private theorem coprimeProduct {z : ℕ} (a : ¬3∣z) (b : ¬5∣z) (c : ¬7∣z) (n : ℕ) :
    Nat.Coprime (3^n*5*7) z := by
  have h3 := (Nat.prime_three.coprime_iff_not_dvd.mpr a).pow_left n
  have h5 := (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr b
  have h7 := (by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr c
  exact (h3.mul_left h5).mul_left h7

/-- Numerical exclusions of the three odd prime orders suffice for the smaller covers. -/
theorem smallOrbit {G X : Type*} [Group G] [Finite G] [MulAction G X] (x : X)
    (size : Nat.card G=241920)
    (away : ∀g : G,orderOf g=3 ∨ orderOf g=5 ∨ orderOf g=7 → g • x≠x) :
    945 ∣ Nat.card (orbit G x) := by
  have a := primeAbsent x Nat.prime_three (fun g h => away g (Or.inl h))
  have b := primeAbsent x (by decide : Nat.Prime 5) (fun g h => away g (Or.inr (Or.inl h)))
  have c := primeAbsent x (by decide : Nat.Prime 7) (fun g h => away g (Or.inr (Or.inr h)))
  apply (coprimeProduct a b c 3).dvd_of_dvd_mul_right
  rw [cardProduct,size]
  decide

/-- If order-three elements have no fixed vertex in an action on 42 vertices,
nine cannot divide the group order. Each vertex orbit would otherwise have size divisible by nine. -/
theorem noNine {H Y : Type*} [Group H] [Finite H] [MulAction H Y] [Finite Y]
    (vertices : Nat.card Y=42) (free : ∀g : H,orderOf g=3 → ∀y : Y,g • y≠y) : ¬9∣Nat.card H := by
  classical
  intro nine
  let _ := Fintype.ofFinite H
  let _ := Fintype.ofFinite Y
  let _ := Fintype.ofFinite (orbitRel.Quotient H Y)
  have all (y : Y) : 9 ∣ Fintype.card H / Fintype.card (stabilizer H y) := by
    have h := primeAbsent y Nat.prime_three (fun g h => free g h y)
    have cop : Nat.Coprime 9 (Nat.card (stabilizer H y)) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr h).pow_left 2
    have dv := cop.dvd_of_dvd_mul_right (cardProduct (G:=H) y ▸ nine)
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,←cardProduct (G:=H) y]
    rw [Nat.mul_div_cancel _ Nat.card_pos]
    exact dv
  have div : 9 ∣ Fintype.card Y := by
    rw [card_eq_sum_card_group_div_card_stabilizer H Y]
    exact Finset.dvd_sum fun w _ => all w.out
  rw [←Nat.card_eq_fintype_card,vertices] at div
  omega

/-- The 42-vertex action can include symmetries that exchange rows and columns. -/
theorem fifteenOrbit {G X Y : Type*} [Group G] [Finite G] [MulAction G X] [MulAction G Y] [Finite Y]
    (x : X) (size : Nat.card G=241920) (vertices : Nat.card Y=42)
    (away : ∀ g : G,orderOf g=5 ∨ orderOf g=7 → g • x≠x)
    (three : ∀g : G,orderOf g=3 → g • x=x → ∀y : Y,g • y≠y) :
    315 ∣ Nat.card (orbit G x) := by
  let H := stabilizer G x
  have nine : ¬9∣Nat.card H := noNine (H:=H) vertices (fun g h y =>
    three g ((Subgroup.orderOf_coe g).trans h) (mem_stabilizer_iff.mp g.property) y)
  have b := primeAbsent x (by decide : Nat.Prime 5) (fun g h => away g (Or.inl h))
  have c := primeAbsent x (by decide : Nat.Prime 7) (fun g h => away g (Or.inr h))
  have product : Nat.card (orbit G x)*Nat.card H=241920 := (cardProduct x).trans size
  by_cases a : 3∣Nat.card H
  · obtain ⟨k,eq⟩ := a
    have a' : ¬3∣k := by omega
    have div : k∣Nat.card H := by rw [eq]; exact dvd_mul_left _ _
    have h := coprimeProduct a' (fun d => b (d.trans div)) (fun d => c (d.trans div)) 2
    apply h.dvd_of_dvd_mul_right
    have smaller : (Nat.card (orbit G x)*k)*3=80640*3 := by
      simpa only [eq,Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using product
    rw [Nat.mul_right_cancel (by decide : 0<3) smaller]
    decide
  · apply (coprimeProduct a b c 2).dvd_of_dvd_mul_right
    rw [product]
    decide

/-- A fixed-point-free involution contributes a factor of two independently of the odd divisor. -/
theorem thirteenOrbit {T : Type*} [Finite T] (f : T → T) (twice : Function.Involutive f)
    (free : ∀ x, f x ≠ x) (oddDivisor : 945 ∣ Nat.card T) : 1890 ∣ Nat.card T := by
  classical
  let _ := Fintype.ofFinite T
  have pairs (s : Finset T) (closed : ∀x∈s,f x∈s) : 2∣s.card := by
    induction s using Finset.strongInductionOn
    rename_i s ih
    by_cases e : s=∅
    · simp [e]
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr e
    let pair : Finset T := {x,f x}
    let rest := s \ pair
    have sub : pair ⊆ s := by
      intro z hz
      simp only [pair,Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact closed x hx
    have small : rest ⊂ s := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset,?_⟩
      intro h
      have hr : x∈rest := h ▸ hx
      exact (Finset.mem_sdiff.mp hr).2 (by simp [pair])
    have stable : ∀z∈rest,f z∈rest := by
      intro z hz
      obtain ⟨sz,out⟩ := Finset.mem_sdiff.mp hz
      refine Finset.mem_sdiff.mpr ⟨closed z sz,?_⟩
      simp only [pair,Finset.mem_insert,Finset.mem_singleton] at out ⊢
      rintro (hit|hit)
      · exact out (Or.inr (by simpa only [twice z] using congrArg f hit))
      · exact out (Or.inl (twice.injective hit))
    have smaller := ih rest small stable
    have cover := Finset.card_sdiff_add_card_eq_card sub
    have card : pair.card=2 := by simp [pair,Ne.symm (free x)]
    change rest.card+pair.card=s.card at cover
    omega
  have even : 2 ∣ Nat.card T := by
    simpa [Nat.card_eq_fintype_card] using pairs Finset.univ (by simp)
  omega

/-- Sum the orbits of a subgroup acting on the entire collection of images.
The index bound is uniform over every image in that collection. -/
theorem orbitMultiplier {Q T : Type*} [Group Q] [Finite Q] [MulAction Q T] [Finite T]
    (m d : ℕ) (size : Nat.card Q=m*d)
    (small : ∀t : T,Nat.card (stabilizer Q t) ∣ d) : m ∣ Nat.card T := by
  classical
  let _ := Fintype.ofFinite Q
  let _ := Fintype.ofFinite T
  let _ := Fintype.ofFinite (orbitRel.Quotient Q T)
  have each (t : T) : m ∣ Fintype.card Q / Fintype.card (stabilizer Q t) := by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,size]
    obtain ⟨k,hk⟩ := small t
    rw [hk,show m*(Nat.card (stabilizer Q t)*k)=(m*k)*Nat.card (stabilizer Q t) by ac_rfl,
      Nat.mul_div_cancel _ Nat.card_pos]
    exact dvd_mul_right _ _
  rw [Nat.card_eq_fintype_card,card_eq_sum_card_group_div_card_stabilizer Q T]
  exact Finset.dvd_sum fun w _ => each w.out

#print axioms orbitMultiplier
#print axioms thirteenOrbit
#print axioms smallOrbit
#print axioms noNine
#print axioms fifteenOrbit
end Checkpoint135.OrbitDivisibility
