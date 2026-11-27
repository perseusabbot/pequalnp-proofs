import PEqualNP.Outside.L_meta_9338
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace Checkpoint137

open Finset PEqualNP.Outside.L_meta_9338

abbrev degree (T : Finset Box) (i : V) := (T.filter (fun b => i ∈ b.1)).card

def covers (T : Finset Box) := ∀ i j, bit i j = false → ∃ b ∈ T, hit b i j

def six (T : Finset Box) := ∀ b ∈ T, b.1.card = 6 ∧ b.2.card = 6

theorem incidences (T : Finset Box) (size : six T) :
    ∑ i : V, degree T i = 6 * T.card := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := T) (t := (univ : Finset V)) (fun (b : Box) (i : V) => i ∈ b.1)
  change (∑ b ∈ T, (univ.filter (fun i : V => i ∈ b.1)).card) = ∑ i : V, degree T i at h
  rw [← h]
  calc
    _ = ∑ _b ∈ T, 6 := sum_congr rfl fun b hb => by simpa using (size b hb).1
    _ = _ := by simp [Nat.mul_comm]

set_option maxHeartbeats 0 in
private theorem zerosPerRow : ∀ i : V, (univ.filter (fun j : V => bit i j = false)).card = 16 := by
  decide +kernel

theorem atLeastThree (T : Finset Box) (size : six T) (complete : covers T) (i : V) :
    3 ≤ degree T i := by
  let through := T.filter (fun b => i ∈ b.1)
  have subset : univ.filter (fun j : V => bit i j = false) ⊆ through.biUnion Prod.snd := by
    intro j hj
    obtain ⟨b, hb, hi, hq⟩ := complete i j (mem_filter.mp hj).2
    exact mem_biUnion.mpr ⟨b, mem_filter.mpr ⟨hb,hi⟩, hq⟩
  have h := (card_le_card subset).trans (card_biUnion_le_card_mul through Prod.snd 6
    (fun b hb => ((size b (mem_filter.mp hb).1).2).le))
  rw [zerosPerRow] at h
  change 16 ≤ degree T i * 6 at h
  omega

theorem threeOrFour (T : Finset Box) (size : six T) (complete : covers T) (limit : T.card ≤ 15) :
    (∃ i, degree T i = 3) ∨ ((∀ i, 4 ≤ degree T i) ∧ ∃ i, degree T i = 4) := by
  by_cases three : ∃ i, degree T i = 3
  · exact Or.inl three
  right
  have four : ∀ i, 4 ≤ degree T i := by
    intro i
    have least := atLeastThree T size complete i
    have ne : degree T i ≠ 3 := fun e => three ⟨i,e⟩
    omega
  refine ⟨four, ?_⟩
  by_contra h
  have five : ∀ i, 5 ≤ degree T i := by
    intro i
    have least := four i
    have ne : degree T i ≠ 4 := fun e => h ⟨i,e⟩
    omega
  have total := sum_le_sum (s := (univ : Finset V)) (f := fun _ => 5) (g := degree T) (fun i _ => five i)
  rw [incidences T size] at total
  simp at total
  omega

theorem allFourAtFourteen (T : Finset Box) (size : six T) (limit : T.card ≤ 14)
    (least : ∀ i, 4 ≤ degree T i) (i : V) : degree T i = 4 := by
  have lo := sum_le_sum (s := (univ : Finset V).erase i) (f := fun _ => 4)
    (g := degree T) (fun j _ => least j)
  have add := sum_erase_add (univ : Finset V) (degree T) (mem_univ i)
  have count : ((univ : Finset V).erase i).card = 20 := by simp
  simp only [sum_const, count, nsmul_eq_mul] at lo
  rw [incidences T size] at add
  have hi := least i
  omega

/-- Three six-sets meeting pairwise can cover sixteen positions only around a single common point. -/
theorem tightTriple {A B C : Finset V} (ha : A.card = 6) (hb : B.card = 6) (hc : C.card = 6)
    (ab : 0 < (A ∩ B).card) (ac : 0 < (A ∩ C).card) (bc : 0 < (B ∩ C).card)
    (full : (A ∪ B ∪ C).card = 16) :
    (A ∩ B).card = 1 ∧ (A ∩ C).card = 1 ∧ (B ∩ C).card = 1 ∧ (A ∩ B ∩ C).card = 1 := by
  have h₁ := card_union_add_card_inter A B
  have h₂ := card_union_add_card_inter (A ∪ B) C
  have h₃ := card_union_add_card_inter (A ∩ C) (B ∩ C)
  have un : (A ∪ B) ∩ C = A ∩ C ∪ B ∩ C := by
    ext x
    simp only [mem_inter, mem_union]
    tauto
  have it : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x
    simp only [mem_inter]
    tauto
  rw [← un,it] at h₃
  have left := card_le_card (inter_subset_left (s₁ := A ∩ B) (s₂ := C))
  have mid : (A ∩ B ∩ C).card ≤ (A ∩ C).card := card_le_card (by
    intro x hx
    exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hx).1).1,(mem_inter.mp hx).2⟩)
  have right : (A ∩ B ∩ C).card ≤ (B ∩ C).card := card_le_card (by
    intro x hx
    exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hx).1).2,(mem_inter.mp hx).2⟩)
  omega

/-- Choose permitted extensions and discard duplicates. -/
theorem extendFamily (T allowed : Finset Box) (possible : ∀ b ∈ T, ∃ c ∈ allowed, fits b c) :
    ∃ U ⊆ allowed, U.card ≤ T.card ∧ ∀ b ∈ T, ∃ c ∈ U, fits b c := by
  classical
  let extend (b : {x // x ∈ T}) := Classical.choose (possible b.val b.property)
  have good (b : {x // x ∈ T}) : extend b ∈ allowed ∧ fits b.val (extend b) :=
    Classical.choose_spec (possible b.val b.property)
  refine ⟨T.attach.image extend, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨b, _, rfl⟩ := mem_image.mp hc
    exact (good b).1
  · simpa using (card_image_le (s := T.attach) (f := extend))
  · intro b hb
    let x : {y // y ∈ T} := ⟨b,hb⟩
    exact ⟨extend x,mem_image.mpr ⟨x,mem_attach _ _,rfl⟩,(good x).2⟩

theorem isolateException (T allowed : Finset Box) (e anchor : Box) (he : e ∈ T) (enlarge : fits e anchor)
    (complete : covers T) (others : ∀ b ∈ T, b ≠ e → ∃ c ∈ allowed, fits b c) :
    ∃ U ⊆ allowed, U.card < T.card ∧ ∀ i j, bit i j = false →
      hit anchor i j ∨ ∃ c ∈ U, hit c i j := by
  obtain ⟨U, subset, bound, extend⟩ := extendFamily (T.erase e) allowed (by
    intro b hb
    exact others b (mem_erase.mp hb).2 (mem_erase.mp hb).1)
  refine ⟨U,subset,lt_of_le_of_lt bound (card_erase_lt_of_mem he),?_⟩
  intro i j zero
  obtain ⟨b, hb, hi, hj⟩ := complete i j zero
  by_cases equal : b = e
  · subst b
    exact Or.inl ⟨enlarge.1 hi,enlarge.2 hj⟩
  · obtain ⟨c,hc,inside⟩ := extend b (mem_erase.mpr ⟨equal,hb⟩)
    exact Or.inr ⟨c,hc,inside.1 hi,inside.2 hj⟩

def witness (i : Fin 16) : H :=
  ([11,32,33,41,43,48,61,68,88,108,109,126,140,152,157,160] : List H).getD i.val 0

set_option maxHeartbeats 0 in
theorem sixteenCover :
    (∀ a b : Fin 16, oval (witness a) = oval (witness b) → a = b) ∧
    (∀ a : Fin 16, (oval (witness a)).1.card = 6 ∧ (oval (witness a)).2.card = 6) ∧
    (∀ (a : Fin 16) (i j : V), hit (oval (witness a)) i j → bit i j = false) ∧
    ∀ i j : V, bit i j = false → ∃ a : Fin 16, hit (oval (witness a)) i j := by
  unfold hit
  decide +kernel

#print axioms incidences
#print axioms atLeastThree
#print axioms threeOrFour
#print axioms allFourAtFourteen
#print axioms tightTriple
#print axioms extendFamily
#print axioms isolateException
#print axioms sixteenCover

end Checkpoint137
