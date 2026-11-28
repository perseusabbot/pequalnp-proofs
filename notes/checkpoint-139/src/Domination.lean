import Degrees
import Overlaps

namespace Checkpoint139

open Finset PEqualNP.Outside.L_meta_9338 Checkpoint138

def lowRows (F : Finset H) := univ.filter (fun p => degree F rside p ≤ 2)
def lowCols (F : Finset H) := univ.filter (fun q => degree F cside q ≤ 2)

def dominates (P L : Finset V) :=
  (∀ p, p ∈ P ∨ ∃ q ∈ L, bit p q = true) ∧
  (∀ q, q ∈ L ∨ ∃ p ∈ P, bit p q = true)

set_option maxHeartbeats 0 in
theorem planeFacts :
    (∀ p, (lines p).card = 5) ∧ (∀ q, (points q).card = 5) ∧
    (∀ p r, ∃ q, q ∈ lines p ∧ q ∈ lines r) ∧
    (∀ q s, ∃ p, p ∈ points q ∧ p ∈ points s) := by decide +kernel

private theorem lowNeighbor {m d : ℕ} (a : V → ℕ) (U : Finset V) (small : m ≤ 10)
    (five : U.card = 5) (balance : 2*d + ∑ i ∈ U, a i = 2*m) :
    d ≤ 2 ∨ ∃ i ∈ U, a i ≤ 2 := by
  by_cases low : d ≤ 2
  · exact Or.inl low
  right
  by_contra! no
  have le := sum_le_sum (s := U) (f := fun _ => 3) (g := a) (fun i hi => no i hi)
  simp [five] at le
  omega

theorem lowDomination (F : Finset H) (small : F.card ≤ 10) : dominates (lowRows F) (lowCols F) := by
  constructor
  · intro p
    rcases lowNeighbor _ _ small (planeFacts.1 p) (degreeBalance F p).1 with h | ⟨q,hq,h⟩
    · exact Or.inl (mem_filter.mpr ⟨mem_univ _,h⟩)
    · exact Or.inr ⟨q,mem_filter.mpr ⟨mem_univ _,h⟩,(mem_filter.mp hq).2⟩
  · intro q
    rcases lowNeighbor _ _ small (planeFacts.2.1 q) (degreeBalance F q).2 with h | ⟨p,hp,h⟩
    · exact Or.inl (mem_filter.mpr ⟨mem_univ _,h⟩)
    · exact Or.inr ⟨p,mem_filter.mpr ⟨mem_univ _,h⟩,(mem_filter.mp hp).2⟩

theorem pencilBound (pencil : V → Finset V) (five : ∀ v, (pencil v).card = 5)
    (common : ∀ a b, ∃ x, x ∈ pencil a ∧ x ∈ pencil b) (S : Finset V) :
    (S.biUnion pencil).card ≤ 4*S.card+1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [biUnion_insert,card_insert_of_notMem ha]
    rcases s.eq_empty_or_nonempty with rfl | ⟨b,hb⟩
    · simp [five]
    · obtain ⟨x,hx,hy⟩ := common a b
      have pos : 0 < (pencil a ∩ s.biUnion pencil).card :=
        card_pos.mpr ⟨x,mem_inter.mpr ⟨hx,mem_biUnion.mpr ⟨b,hb,hy⟩⟩⟩
      have add := card_union_add_card_inter (pencil a) (s.biUnion pencil)
      rw [five] at add
      omega

theorem spans {P L : Finset V} (h : dominates P L) :
    P ∪ L.biUnion points = univ ∧ L ∪ P.biUnion lines = univ := by
  constructor
  · apply eq_univ_of_forall
    intro p
    rcases h.1 p with hp | ⟨q,hq,i⟩
    · exact mem_union_left _ hp
    · exact mem_union_right _ (mem_biUnion.mpr ⟨q,hq,mem_filter.mpr ⟨mem_univ _,i⟩⟩)
  · apply eq_univ_of_forall
    intro q
    rcases h.2 q with hq | ⟨p,hp,i⟩
    · exact mem_union_left _ hq
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨mem_univ _,i⟩⟩)

theorem dominatingEight {P L : Finset V} (h : dominates P L) : 8 ≤ P.card + L.card := by
  have a := pencilBound lines planeFacts.1 planeFacts.2.2.1 P
  have b := pencilBound points planeFacts.2.1 planeFacts.2.2.2 L
  have s := card_union_le P (L.biUnion points)
  have t := card_union_le L (P.biUnion lines)
  rw [(spans h).1] at s
  rw [(spans h).2] at t
  simp at s t
  omega

/-- Equality gives a maximal four-by-four zero rectangle, by mutual complementation. -/
theorem equalityBox {P L : Finset V} (h : dominates P L) (size : P.card + L.card = 8) :
    P.card = 4 ∧ L.card = 4 ∧ legal (P,L) ∧
    (∀ p ∉ P, ∃ q ∈ L, bit p q = true) ∧ (∀ q ∉ L, ∃ p ∈ P, bit p q = true) := by
  have a := pencilBound lines planeFacts.1 planeFacts.2.2.1 P
  have b := pencilBound points planeFacts.2.1 planeFacts.2.2.2 L
  have s := card_union_add_card_inter P (L.biUnion points)
  have t := card_union_add_card_inter L (P.biUnion lines)
  rw [(spans h).1] at s
  rw [(spans h).2] at t
  simp only [card_univ,Fintype.card_fin] at s t
  refine ⟨by omega, by omega, ?_, fun p hp => (h.1 p).resolve_left hp, fun q hq => (h.2 q).resolve_left hq⟩
  intro p hp q hq
  by_contra! pos
  have inQ : p ∈ points q := mem_filter.mpr ⟨mem_univ _,by simpa using pos⟩
  have some : 0 < (P ∩ L.biUnion points).card :=
    card_pos.mpr ⟨p,mem_inter.mpr ⟨hp,mem_biUnion.mpr ⟨q,hq,inQ⟩⟩⟩
  omega

theorem eightLowLabels (F : Finset H) (small : F.card ≤ 10) :
    8 ≤ (lowRows F).card + (lowCols F).card := dominatingEight (lowDomination F small)

set_option maxHeartbeats 0 in
theorem sixSides : ∀ h : H, (rside h).card = 6 ∧ (cside h).card = 6 := by decide +kernel

private theorem atMostEleven (T : Finset H) (side : H → Finset V) (six : ∀ h, (side h).card = 6)
    (pair : ∀ h ∈ T, ∀ k ∈ T, 0 < (side h ∩ side k).card) (low : T.card ≤ 2) :
    (T.biUnion side).card ≤ 11 := by
  by_cases two : T.card = 2
  · obtain ⟨a,b,ne,eq⟩ := card_eq_two.mp two
    have ab := pair a (by simp [eq]) b (by simp [eq])
    have add := card_union_add_card_inter (side a) (side b)
    rw [six,six] at add
    simpa [eq] using (show (side a ∪ side b).card ≤ 11 by omega)
  · have bound := card_biUnion_le_card_mul T side 6 (fun h _ => (six h).le)
    omega

def coveredRow (F : Finset H) (p : V) := (F.filter (fun h => p ∈ rside h)).biUnion cside
def coveredCol (F : Finset H) (q : V) := (F.filter (fun h => q ∈ cside h)).biUnion rside

theorem elevenAtLowRow (F : Finset H) {p : V} (hp : p ∈ lowRows F) : (coveredRow F p).card ≤ 11 := by
  apply atMostEleven _ _ (fun h => (sixSides h).2) _ (mem_filter.mp hp).2
  intro h hh k hk
  have overlap : 0 < (rside h ∩ rside k).card :=
    card_pos.mpr ⟨p,mem_inter.mpr ⟨(mem_filter.mp hh).2,(mem_filter.mp hk).2⟩⟩
  exact (Checkpoint137.balancedPairs h k) ▸ overlap

theorem elevenAtLowCol (F : Finset H) {q : V} (hq : q ∈ lowCols F) : (coveredCol F q).card ≤ 11 := by
  apply atMostEleven _ _ (fun h => (sixSides h).1) _ (mem_filter.mp hq).2
  intro h hh k hk
  have overlap : 0 < (cside h ∩ cside k).card :=
    card_pos.mpr ⟨q,mem_inter.mpr ⟨(mem_filter.mp hh).2,(mem_filter.mp hk).2⟩⟩
  exact (show (rside h ∩ rside k).card = (cside h ∩ cside k).card from Checkpoint137.balancedPairs h k).symm ▸ overlap

#print axioms lowDomination
#print axioms dominatingEight
#print axioms equalityBox
#print axioms eightLowLabels
#print axioms elevenAtLowRow
#print axioms elevenAtLowCol

end Checkpoint139
