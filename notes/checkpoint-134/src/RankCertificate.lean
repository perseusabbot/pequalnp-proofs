import PEqualNP.Outside.L_meta_9338

namespace Checkpoint134
open Finset
open PEqualNP.Outside.L_meta_9338 (encode encodeAdd readDigit)

abbrev digit := PEqualNP.Outside.L_meta_9338.component
abbrev Base := 16777216
abbrev Guard := 8388608
abbrev Width := 24

structure Book (m : ℕ) where
  n : ℕ
  coin : Fin m → ℕ
  fill : ℕ
  flags : ℕ
  total : ℕ

def weight {m} (b : Book m) (k : ℕ) (j : Fin m) := digit Base k (b.coin j)
def cap {m} (b : Book m) (k : ℕ) := Guard-1-digit Base k b.fill
def tally {m} (values : Fin m → ℕ) (mask : ℕ) :=
  ∑ j : Fin m, if mask.testBit j.val then values j else 0

structure Sound {m} (b : Book m) : Prop where
  words : ∀ j, b.coin j < Base^b.n
  filler : b.fill < Base^b.n
  offset : ∀ k : Fin b.n, digit Base k b.fill < Guard
  marked : ∀ k : Fin b.n, b.flags.testBit (Width*k.val+23) = true
  mass : ∀ k : Fin b.n, (∑ j,weight b k j) = digit Base k b.total
  bound : ∀ k : Fin b.n, digit Base k b.total < Guard

theorem tallySmall {m} {b : Book m} (s : Sound b) (mask : ℕ) (k : Fin b.n) :
    tally (weight b k) mask < Guard := by
  apply lt_of_le_of_lt _ (s.bound k)
  rw [←s.mass]
  exact sum_le_sum (fun j _ => by by_cases h : mask.testBit j.val <;> simp [h])

theorem encodeTally {m} (n : ℕ) (v : ℕ → Fin m → ℕ) (mask : ℕ) :
    encode Base n (fun i => tally (v i) mask) =
      tally (fun j => encode Base n (fun i => v i j)) mask := by
  induction n generalizing v with
  | zero => simp [PEqualNP.Outside.L_meta_9338.encode,tally]
  | succ n ih =>
    rw [encode,ih]
    simp only [tally,encode,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    by_cases h : mask.testBit j.val <;> simp [h]

theorem packedTally {m} {b : Book m} (s : Sound b) (mask : ℕ) :
    encode Base b.n (fun i => tally (weight b i) mask) = tally b.coin mask := by
  rw [encodeTally]
  simp [weight,PEqualNP.Outside.L_meta_9338.encodeWord,Nat.mod_eq_of_lt (s.words _)]

theorem readScore {m} {b : Book m} (s : Sound b) (mask : ℕ) (k : Fin b.n) :
    digit Base k (tally b.coin mask) = tally (weight b k) mask := by
  rw [←packedTally s]
  exact readDigit _ _ _ (fun i hi => lt_trans (tallySmall s _ ⟨i,hi⟩) (by decide)) k.isLt

def Passed {m} (b : Book m) (score rank count : ℕ) : Bool :=
  decide (rank < b.n) &&
  ((score + b.fill) &&& (b.flags % 2^(Width*(rank+1))) == 0) &&
  decide (digit Base rank score + (count-1)*cap b rank < digit Base rank b.total)

theorem prefixCap {m} {b : Book m} (s : Sound b) (mask rank count : ℕ)
    (pass : Passed b (tally b.coin mask) rank count = true)
    (k : Fin b.n) (le : k.val ≤ rank) : tally (weight b k) mask ≤ cap b k := by
  simp only [Passed,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at pass
  have bit := congrArg (fun x : ℕ => x.testBit (Width*k.val+23)) pass.1.2
  have boundBit : Width*k.val+23 < Width*(rank+1) := by change 24*k.val+23<24*(rank+1); omega
  have no : (tally b.coin mask + b.fill).testBit (Width*k.val+23) = false := by
    simpa only [Nat.testBit_and,Nat.testBit_mod_two_pow,decide_eq_true boundBit,
      Bool.true_and,s.marked k,Bool.and_true,Nat.zero_testBit] using bit
  let f := fun i => tally (weight b i) mask
  let g := fun i => digit Base i b.fill
  have small (i) (hi : i<b.n) : f i + g i < Base := by
    have a := tallySmall s mask ⟨i,hi⟩
    have c := s.offset ⟨i,hi⟩
    change tally (weight b i) mask + digit Base i b.fill < Base
    simp only [Base,Guard] at a c ⊢
    omega
  have rd := readDigit Base b.n (fun i => f i + g i) small k.isLt
  rw [encodeAdd,show encode Base b.n f=tally b.coin mask from packedTally s mask,
    show encode Base b.n g=b.fill from (PEqualNP.Outside.L_meta_9338.encodeWord _ _ _).trans (Nat.mod_eq_of_lt s.filler)] at rd
  have guardBit : (digit Base k (tally b.coin mask+b.fill)).testBit 23 = false := by
    change ((((tally b.coin mask+b.fill) / (2^Width)^k.val) % 2^Width)).testBit 23 = false
    rw [←pow_mul,←Nat.shiftRight_eq_div_pow]
    simp only [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,show decide (23<Width)=true from rfl,Bool.true_and,no]
  change digit Base k (tally b.coin mask+b.fill) = f k.val + g k.val at rd
  rw [rd,Nat.testBit_eq_decide_div_mod_eq] at guardBit
  have a := of_decide_eq_false guardBit
  have h := small k.val k.isLt
  have c := s.offset k
  change ¬ ((tally (weight b k.val) mask + digit Base k.val b.fill) / Guard % 2 = 1) at a
  change tally (weight b k.val) mask + digit Base k.val b.fill < Base at h
  unfold cap
  simp only [Base,Guard] at a h c ⊢
  omega

theorem rankedImpossible {m N} {b : Book m} (s : Sound b) (count : ℕ) (positive : 0<count)
    (masks ranks : Fin N → ℕ) (checks : ∀ i, Passed b (tally b.coin (masks i)) (ranks i) count = true)
    (chosen : Fin count → Fin N)
    (covers : ∀ j, b.coin j≠0 → ∃ t,(masks (chosen t)).testBit j.val=true) : False := by
  let first : Fin count := ⟨0,positive⟩
  obtain ⟨t,_,least⟩ := Finset.exists_min_image (univ : Finset (Fin count))
    (fun t => ranks (chosen t)) ⟨first,mem_univ _⟩
  have ht := checks (chosen t)
  simp only [Passed,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ht
  let k : Fin b.n := ⟨ranks (chosen t),ht.1.1⟩
  have upper (u : Fin count) : tally (weight b k) (masks (chosen u)) ≤ cap b k :=
    prefixCap s _ _ _ (checks _) k (least u (mem_univ _))
  have below := ht.2
  rw [show digit Base (ranks (chosen t)) (tally b.coin (masks (chosen t))) =
    tally (weight b k) (masks (chosen t)) from readScore s _ k] at below
  have summed : (∑ j,weight b k j) ≤ ∑ u, tally (weight b k) (masks (chosen u)) := by
    simp only [tally]
    rw [sum_comm]
    apply sum_le_sum
    intro j _
    by_cases z : b.coin j=0
    · simp [weight,z,digit,PEqualNP.Outside.L_meta_9338.component]
    · obtain ⟨u,hu⟩ := covers j z
      have one := single_le_sum (f := fun v : Fin count => if (masks (chosen v)).testBit j.val then weight b k j else 0)
        (fun i _ => Nat.zero_le _) (mem_univ u)
      simpa only [hu,ite_true] using one
  rw [s.mass k] at summed
  have rest := sum_le_sum (s := (univ : Finset (Fin count)).erase t) (fun i _ => upper i)
  rw [sum_const,nsmul_eq_mul,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at rest
  have all := sum_erase_add (univ : Finset (Fin count)) (fun u => tally (weight b k) (masks (chosen u))) (mem_univ t)
  change tally (weight b k) (masks (chosen t)) + (count-1)*cap b k < digit Base k b.total at below
  have sumBound := (Nat.add_le_add_right rest (tally (weight b k) (masks (chosen t))))
  rw [all,Nat.add_comm] at sumBound
  exact (Nat.not_lt_of_ge (summed.trans sumBound)) below

#print axioms rankedImpossible
end Checkpoint134
