import Board
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace Checkpoint138

open PEqualNP.Outside.L_meta_9338 Finset

def lines (p : V) := univ.filter (fun q : V => bit p q = true)
def points (q : V) := univ.filter (fun p : V => bit p q = true)

abbrev degree (F : Finset H) (side : H → Finset V) (p : V) := (F.filter (fun h => p ∈ side h)).card
abbrev rside (h : H) := (oval h).1
abbrev cside (h : H) := (oval h).2

set_option maxHeartbeats 0 in
private theorem sizes : ∀ h : H, (rside h).card = 6 ∧ (cside h).card = 6 := by decide +kernel

set_option maxHeartbeats 0 in
private theorem plane : (∀ q : V, (points q).card = 5) ∧
    (∀ p r : V, ∃ q, p ∈ points q ∧ r ∈ points q) := by decide +kernel

set_option maxHeartbeats 0 in
private theorem boxBalance : ∀ (h : H) (v : V),
    (2*(if v ∈ rside h then 1 else 0) + (lines v ∩ cside h).card = 2) ∧
    (2*(if v ∈ cside h then 1 else 0) + (points v ∩ rside h).card = 2) := by decide +kernel

private theorem localCount (F : Finset H) (side : H → Finset V) (U : Finset V) :
    ∑ v ∈ U, degree F side v = ∑ h ∈ F, (U ∩ side h).card := by
  have d := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := F) (t := U) (fun h v => v ∈ side h)
  change (∑ h ∈ F, (U.filter (fun v => v ∈ side h)).card) = ∑ v ∈ U, degree F side v at d
  rw [← d]
  apply sum_congr rfl
  intro h _
  congr 1

private theorem balanceSum (F : Finset H) (first other : H → Finset V) (v : V) (U : Finset V)
    (identity : ∀ h : H, 2*(if v ∈ first h then 1 else 0) + (U ∩ other h).card = 2) :
    2*degree F first v + ∑ x ∈ U, degree F other x = 2*F.card := by
  rw [localCount]
  have deg : degree F first v = ∑ h ∈ F, (if v ∈ first h then 1 else 0) := by
    simp [degree,Finset.sum_boole]
  rw [deg,mul_sum,←sum_add_distrib]
  calc
    _ = ∑ _h ∈ F, 2 := sum_congr rfl (fun h _ => identity h)
    _ = _ := by simp [Nat.mul_comm]

theorem degreeBalance (F : Finset H) (v : V) :
    (2*degree F rside v + ∑ x ∈ lines v, degree F cside x = 2*F.card) ∧
    (2*degree F cside v + ∑ x ∈ points v, degree F rside x = 2*F.card) :=
  ⟨balanceSum F _ _ v _ (fun h => (boxBalance h v).1),
   balanceSum F _ _ v _ (fun h => (boxBalance h v).2)⟩

private theorem sixSum (F : Finset H) (side : H → Finset V) (six : ∀ h, (side h).card = 6) :
    ∑ v : V, degree F side v = 6*F.card := by
  rw [localCount]
  simp [six,Nat.mul_comm]

def heavy (d : V → ℕ) := univ.filter (fun v => 5 ≤ d v)

theorem surplusBox (F : Finset H) (number : F.card = 15)
    (rows : ∀ v, 4 ≤ degree F rside v) (cols : ∀ v, 4 ≤ degree F cside v) :
    (heavy (degree F rside)).card = 6 ∧ (heavy (degree F cside)).card = 6 ∧
    legal (heavy (degree F rside),heavy (degree F cside)) ∧
    (∀ v, degree F rside v ≤ 5) ∧ (∀ v, degree F cside v ≤ 5) := by
  let r (p : V) := degree F rside p - 4
  let c (q : V) := degree F cside q - 4
  have minusFour (d : V → ℕ) (lo : ∀ p, 4 ≤ d p) (U : Finset V) :
      (∑ p ∈ U, (d p-4)) + U.card*4 = ∑ p ∈ U, d p := by
    calc
      _ = (∑ p ∈ U, (d p-4)) + ∑ _p ∈ U, 4 := by simp
      _ = ∑ p ∈ U, ((d p-4)+4) := sum_add_distrib.symm
      _ = _ := sum_congr rfl fun p _ => Nat.sub_add_cancel (lo p)
  have sumSix (d : V → ℕ) (lo : ∀ p, 4 ≤ d p) (total : ∑ p, d p = 6*F.card) :
      ∑ p, (d p-4) = 6 := by
    have h := minusFour d lo univ
    rw [total,number] at h
    simp at h
    omega
  have rs : ∑ p, r p = 6 := sumSix _ rows (sixSum F rside (fun h => (sizes h).1))
  have cs : ∑ q, c q = 6 := sumSix _ cols (sixSum F cside (fun h => (sizes h).2))
  have pencil (q : V) : (∑ p ∈ points q, r p)+2*c q = 2 := by
    have h := minusFour _ rows (points q)
    have e := (degreeBalance F q).2
    rw [plane.1 q] at h
    rw [number] at e
    dsimp only [r,c]
    have cq := cols q
    omega
  have pairBound (p q : V) (ne : p ≠ q) : r p+r q ≤ 2 := by
    obtain ⟨l,hp,hq⟩ := plane.2 p q
    have sub : ({p,q} : Finset V) ⊆ points l := by simpa [Finset.insert_subset_iff] using And.intro hp hq
    have le := sum_le_sum_of_subset_of_nonneg (f := r) sub (fun i _ _ => Nat.zero_le (r i))
    simp [ne] at le
    have h := pencil l
    omega
  have r1 (p : V) : r p ≤ 1 := by
    by_contra! large
    have only (q : V) (ne : q ≠ p) : r q = 0 := by
      have h := pairBound q p ne
      omega
    have eq := sum_eq_single (s := (univ : Finset V)) (f := r) p (fun q _ ne => only q ne) (by simp)
    have any := pairBound p (p+1) (by simp)
    omega
  have c1 (q : V) : c q ≤ 1 := by have h := pencil q; omega
  have count (d : V → ℕ) (small : ∀ v, d v-4 ≤ 1) (total : ∑ v, (d v-4) = 6) : (heavy d).card = 6 := by
    rw [← total]
    calc
      _ = ∑ v : V, (if 5 ≤ d v then 1 else 0) := by simp [heavy,Finset.sum_boole]
      _ = _ := sum_congr rfl fun v _ => by split <;> have h := small v <;> omega
  refine ⟨count _ r1 rs,count _ c1 cs,?_,?_,?_⟩
  · intro p hp q hq
    have p5 := (mem_filter.mp hp).2
    have q5 := (mem_filter.mp hq).2
    by_contra! e
    have inside : p ∈ points q := mem_filter.mpr ⟨mem_univ _,by simpa using e⟩
    have le := single_le_sum (f := r) (fun x _ => Nat.zero_le (r x)) inside
    have b := pencil q
    dsimp only [r,c] at le b
    omega
  · intro p
    have h := r1 p
    dsimp only [r] at h
    omega
  · intro q
    have h := c1 q
    dsimp only [c] at h
    omega

#print axioms degreeBalance
#print axioms surplusBox

end Checkpoint138
