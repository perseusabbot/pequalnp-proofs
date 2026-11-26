import RankCertificate

namespace Checkpoint134
open Finset

def Accept {m} (b other : Book m) (own rest score rank : ℕ) :=
  Passed b score rank 1 && decide
    (digit Base rank score + (own-1)*cap b rank + rest*cap other rank < digit Base rank b.total)

theorem tallyCover {m f g} (w : Fin m → ℕ) (a : Fin f → ℕ) (b : Fin g → ℕ)
    (covered : ∀ j, w j≠0 → (∃ i,(a i).testBit j.val=true) ∨ ∃ i,(b i).testBit j.val=true) :
    (∑ j,w j) ≤ (∑ i,tally w (a i)) + ∑ i,tally w (b i) := by
  unfold tally
  rw [sum_comm (s := (univ : Finset (Fin f))),sum_comm (s := (univ : Finset (Fin g))),←sum_add_distrib]
  apply sum_le_sum
  intro j _
  by_cases z : w j=0
  · rw [z]; exact Nat.zero_le _
  · rcases covered j z with ⟨i,hi⟩ | ⟨i,hi⟩
    · apply le_trans _ (Nat.le_add_right ..)
      have one := single_le_sum (f := fun t : Fin f => if (a t).testBit j.val then w j else 0) (fun _ _ => Nat.zero_le _) (mem_univ i)
      simpa only [hi,ite_true] using one
    · apply le_trans _ (Nat.le_add_left ..)
      have one := single_le_sum (f := fun t : Fin g => if (b t).testBit j.val then w j else 0) (fun _ _ => Nat.zero_le _) (mem_univ i)
      simpa only [hi,ite_true] using one

theorem firstRejected {m f g} {b c : Book m} (sb : Sound b) (sc : Sound c)
    (size : b.n=c.n) (coins : b.coin=c.coin) (a ra : Fin f → ℕ) (d rd : Fin g → ℕ)
    (va : ∀i,Accept b c f g (tally b.coin (a i)) (ra i)=true)
    (vd : ∀i,Accept c b g f (tally c.coin (d i)) (rd i)=true)
    (cov : ∀ j,b.coin j≠0 → (∃ i,(a i).testBit j.val=true) ∨ ∃ i,(d i).testBit j.val=true)
    (t : Fin f) (left : ∀ i,ra t≤ra i) (right : ∀ i,ra t≤rd i) : False := by
  have test := (Bool.and_eq_true_iff.mp (va t))
  have below := of_decide_eq_true test.2
  have pass := test.1
  simp only [Passed,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at pass
  let k : Fin b.n := ⟨ra t,pass.1.1⟩
  let l : Fin c.n := ⟨ra t,size ▸ pass.1.1⟩
  have eqw : weight c l = weight b k := by funext j; simp [weight,k,l,coins]
  have A (u : Fin f) : tally (weight b k) (a u) ≤ cap b k :=
    prefixCap sb _ _ _ (Bool.and_eq_true_iff.mp (va u)).1 k (left u)
  have D (u : Fin g) : tally (weight b k) (d u) ≤ cap c l := by
    rw [←eqw]
    exact prefixCap sc _ _ _ (Bool.and_eq_true_iff.mp (vd u)).1 l (right u)
  have lower := tallyCover (weight b k) a d (by
    intro j h
    apply cov j
    intro z
    simp [weight,z,digit,PEqualNP.Outside.L_meta_9338.component] at h)
  rw [sb.mass] at lower
  have erase := sum_le_sum (s := (univ : Finset (Fin f)).erase t) (fun u _ => A u)
  rw [sum_const,nsmul_eq_mul,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at erase
  have allD := sum_le_sum (s := (univ : Finset (Fin g))) (fun u _ => D u)
  rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] at allD
  have A' := Nat.add_le_add_right erase (tally (weight b k) (a t))
  rw [sum_erase_add _ _ (mem_univ t),Nat.add_comm] at A'
  have bound := lower.trans (Nat.add_le_add A' allD)
  rw [show digit Base (ra t) (tally b.coin (a t)) = tally (weight b k) (a t) from readScore sb _ k] at below
  exact (Nat.not_lt_of_ge bound) below

theorem mixedImpossible {m f g} {b c : Book m} (sb : Sound b) (sc : Sound c)
    (size : b.n=c.n) (coins : b.coin=c.coin) (pos : 0<f)
    (a ra : Fin f → ℕ) (d rd : Fin g → ℕ)
    (va : ∀i,Accept b c f g (tally b.coin (a i)) (ra i)=true)
    (vd : ∀i,Accept c b g f (tally c.coin (d i)) (rd i)=true)
    (cov : ∀ j,b.coin j≠0 → (∃ i,(a i).testBit j.val=true) ∨ ∃ i,(d i).testBit j.val=true) : False := by
  obtain ⟨t,_,lo⟩ := exists_min_image (univ : Finset (Fin f ⊕ Fin g)) (Sum.elim ra rd)
    ⟨Sum.inl ⟨0,pos⟩,mem_univ _⟩
  cases t with
  | inl t =>
    exact firstRejected sb sc size coins a ra d rd va vd cov t
      (fun i => lo (Sum.inl i) (mem_univ _)) (fun i => lo (Sum.inr i) (mem_univ _))
  | inr t =>
    exact firstRejected sc sb size.symm coins.symm d rd a ra vd va
      (fun j h => (cov j (coins ▸ h)).symm) t
      (fun i => lo (Sum.inr i) (mem_univ _)) (fun i => lo (Sum.inl i) (mem_univ _))

#print axioms mixedImpossible
end Checkpoint134
