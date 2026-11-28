import Domination
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace Checkpoint139

open Finset PEqualNP.Outside.L_meta_9338 Checkpoint138

theorem disjointDegrees (F : Finset H) {p q : V} (inc : bit p q = true) :
    degree F rside p + degree F cside q ≤ F.card := by
  let A := F.filter (fun h => p ∈ rside h)
  let B := F.filter (fun h => q ∈ cside h)
  have e : A ∩ B = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro h hhit
    obtain ⟨a,b⟩ := mem_inter.mp hhit
    have z := zeroOfInc (x := (p,q)) (h := h) ⟨(mem_filter.mp a).2,(mem_filter.mp b).2⟩
    simp [inc] at z
  have bound := card_le_card (show A ∪ B ⊆ F from union_subset (filter_subset ..) (filter_subset ..))
  have s := card_union_add_card_inter A B
  rw [e,card_empty,add_zero] at s
  change A.card+B.card ≤ F.card
  omega

private theorem total (F : Finset H) (f : H → Finset V) (six : ∀ h, (f h).card = 6) :
    ∑ i : V, degree F f i = 6*F.card := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := F) (t := (univ : Finset V)) (fun h v => v ∈ f h)
  change (∑ h ∈ F, (univ.filter (fun v => v ∈ f h)).card) = ∑ v : V, degree F f v at h
  simpa [six,Nat.mul_comm] using h.symm

private theorem noncollinear (X : V → Finset V) (five : ∀ v, (X v).card = 5)
    (common : ∀ a b, ∃ x, x ∈ X a ∧ x ∈ X b) (a b c d : V)
    (no : ¬ ∃ x, x ∈ X a ∧ x ∈ X b ∧ x ∈ X c) :
    (X a ∪ X b ∪ X c ∪ X d).card ≤ 15 := by
  obtain ⟨u,ua,ub⟩ := common a b
  have ab : 0 < (X a ∩ X b).card := card_pos.mpr ⟨u,mem_inter.mpr ⟨ua,ub⟩⟩
  have cab : 2 ≤ ((X a ∪ X b) ∩ X c).card := by
    by_contra! few
    obtain ⟨x,xa,xc⟩ := common a c
    obtain ⟨y,yb,yc⟩ := common b c
    have e := card_le_one.mp (show ((X a ∪ X b) ∩ X c).card ≤ 1 by omega)
      x (mem_inter.mpr ⟨mem_union_left _ xa,xc⟩) y (mem_inter.mpr ⟨mem_union_right _ yb,yc⟩)
    exact no ⟨x,xa,e ▸ yb,xc⟩
  have dabc : 2 ≤ ((X a ∪ X b ∪ X c) ∩ X d).card := by
    by_contra! few
    obtain ⟨x,xa,xd⟩ := common a d
    obtain ⟨y,yb,yd⟩ := common b d
    obtain ⟨z,zc,zd⟩ := common c d
    have same := card_le_one.mp (show ((X a ∪ X b ∪ X c) ∩ X d).card ≤ 1 by omega)
    have hx : x ∈ (X a ∪ X b ∪ X c) ∩ X d :=
      mem_inter.mpr ⟨mem_union_left _ (mem_union_left _ xa),xd⟩
    have xy := same x hx y (mem_inter.mpr ⟨mem_union_left _ (mem_union_right _ yb),yd⟩)
    have xz := same x hx z (mem_inter.mpr ⟨mem_union_right _ zc,zd⟩)
    exact no ⟨x,xa,xy ▸ yb,xz ▸ zc⟩
  have h₁ := card_union_add_card_inter (X a) (X b)
  have h₂ := card_union_add_card_inter (X a ∪ X b) (X c)
  have h₃ := card_union_add_card_inter (X a ∪ X b ∪ X c) (X d)
  rw [five,five] at h₁
  rw [five] at h₂ h₃
  omega

private theorem fourOnLine (X : V → Finset V) (five : ∀ v, (X v).card = 5)
    (common : ∀ a b, ∃ x, x ∈ X a ∧ x ∈ X b)
    (unique : ∀ a b, a ≠ b → (X a ∩ X b).card = 1)
    {P : Finset V} (four : P.card = 4) (reach : 16 ≤ (P.biUnion X).card) :
    ∃ l, ∀ p ∈ P, l ∈ X p := by
  obtain ⟨a,b,c,d,ab,_,_,_,_,_,rfl⟩ := card_eq_four.mp four
  obtain ⟨l,ha,hb⟩ := common a b
  have only {x : V} (xa : x ∈ X a) (xb : x ∈ X b) : x = l :=
    (card_le_one.mp (unique a b ab).le) x (mem_inter.mpr ⟨xa,xb⟩) l (mem_inter.mpr ⟨ha,hb⟩)
  have lift (u v : V) (r : 16 ≤ (X a ∪ X b ∪ X u ∪ X v).card) : l ∈ X u := by
    by_contra notin
    have n := noncollinear X five common a b u v (by
      rintro ⟨x,xa,xb,xu⟩
      exact notin (only xa xb ▸ xu))
    omega
  have r : 16 ≤ (X a ∪ X b ∪ X c ∪ X d).card := by simpa [union_assoc] using reach
  have hc := lift c d r
  have hd := lift d c (by simpa only [union_right_comm _ (X c) (X d)] using r)
  exact ⟨l,by simpa using And.intro ha (And.intro hb (And.intro hc hd))⟩

set_option maxHeartbeats 0 in
private theorem uniqueness :
    (∀ a b : V, a ≠ b → (lines a ∩ lines b).card = 1) ∧
    (∀ a b : V, a ≠ b → (points a ∩ points b).card = 1) := by decide +kernel

set_option maxHeartbeats 0 in
private theorem throughOnly :
    (∀ l p : V, p ∈ points l → ∃ k, Disjoint ((points l).erase p) (points k)) ∧
    (∀ l p : V, p ∈ lines l → ∃ k, Disjoint ((lines l).erase p) (lines k)) := by decide +kernel

private theorem fourImpossible (D E : V → ℕ) (out back : V → Finset V) (P L : Finset V) (m : ℕ)
    (size : m ≤ 9) (four : P.card = 4) (few : L.card ≤ 5)
    (span : L ∪ P.biUnion out = univ) (high : ∀ i ∉ P, 3 ≤ D i)
    (tot : ∑ p, D p = 6*m)
    (balance : ∀ l, 2*E l + ∑ p ∈ back l, D p = 2*m)
    (apart : ∀ p l, p ∈ back l → D p+E l ≤ m)
    (flip : ∀ p l, l ∈ out p ↔ p ∈ back l)
    (five : ∀ p, (out p).card = 5) (five' : ∀ l, (back l).card = 5)
    (common : ∀ a b, ∃ x, x ∈ out a ∧ x ∈ out b)
    (unique : ∀ a b, a ≠ b → (out a ∩ out b).card = 1)
    (tangent : ∀ l p, p ∈ back l → ∃ k, Disjoint ((back l).erase p) (back k)) : False := by
  classical
  have reach := card_union_le L (P.biUnion out)
  rw [span] at reach
  simp only [card_univ,Fintype.card_fin] at reach
  obtain ⟨l,h⟩ := fourOnLine out five common unique four (by omega)
  have inside : P ⊆ back l := fun p hp => (flip p l).mp (h p hp)
  obtain ⟨p,hp,hpP⟩ : ∃ p ∈ back l, p ∉ P := by
    by_contra! no
    have le := card_le_card no
    rw [four,five'] at le
    omega
  let U := (back l)ᶜ
  have cardU : U.card = 16 := by simp [U,card_compl,five']
  have least (q : V) (hq : q ∈ U) : 3 ≤ D q := high q (fun eq => (mem_compl.mp hq) (inside eq))
  have lb := sum_le_sum (s := U) (f := fun _ => 3) (g := D) least
  simp only [sum_const,cardU,nsmul_eq_mul] at lb
  have sums := sum_add_sum_compl (back l) D
  change (∑ q ∈ back l, D q) + ∑ q ∈ U, D q = ∑ q, D q at sums
  rw [tot] at sums
  have atLine := balance l
  have incident := apart p l hp
  have p3 := high p hpP
  have pd : D p = 3 := by omega
  have eqSum : (∑ q ∈ U, 3) = ∑ q ∈ U, D q := by simp [cardU]; omega
  have uniform (q : V) (hq : q ∈ U) : D q = 3 :=
    ((sum_eq_sum_iff_of_le least).mp eqSum q hq).symm
  obtain ⟨k,hk⟩ := tangent l p hp
  have dis := disjoint_left.mp hk
  have three (q : V) (hq : q ∈ back k) : D q = 3 := by
    by_cases e : q = p
    · exact e ▸ pd
    · apply uniform q
      exact mem_compl.mpr fun ql => dis (mem_erase.mpr ⟨e,ql⟩) hq
  have odd := balance k
  have s : (∑ q ∈ back k, D q) = 15 := by
    calc
      _ = ∑ _q ∈ back k, 3 := sum_congr rfl three
      _ = _ := by simp [five']
  rw [s] at odd
  omega

theorem tenLowLabels (F : Finset H) (small : F.card ≤ 9) :
    10 ≤ (lowRows F).card + (lowCols F).card := by
  let P := lowRows F
  let L := lowCols F
  have d := lowDomination F (by omega)
  have ⟨sp,sl⟩ := spans d
  have a := pencilBound lines planeFacts.1 planeFacts.2.2.1 P
  have b := pencilBound points planeFacts.2.1 planeFacts.2.2.2 L
  have s := card_union_le (lowRows F) ((lowCols F).biUnion points)
  have t := card_union_le (lowCols F) ((lowRows F).biUnion lines)
  rw [sp] at s
  rw [sl] at t
  simp only [card_univ,Fintype.card_fin] at s t
  change 21 ≤ P.card + (L.biUnion points).card at s
  change 21 ≤ L.card + (P.biUnion lines).card at t
  change 10 ≤ P.card+L.card
  by_contra! tooFew
  have cases : (P.card = 4 ∧ L.card ≤ 5) ∨ (L.card = 4 ∧ P.card ≤ 5) := by omega
  rcases cases with ⟨four,few⟩ | ⟨four,few⟩
  · exact fourImpossible (degree F rside) (degree F cside) lines points P L _ small four few sl
      (fun p hp => by change p ∉ lowRows F at hp; simp [lowRows] at hp; omega)
      (total F rside fun h => (sixSides h).1) (fun l => (degreeBalance F l).2)
      (fun p l hp => disjointDegrees F (mem_filter.mp hp).2)
      (by intro p l; simp [lines,points]) planeFacts.1 planeFacts.2.1 planeFacts.2.2.1 uniqueness.1 throughOnly.1
  · exact fourImpossible (degree F cside) (degree F rside) points lines L P _ small four few sp
      (fun l hl => by change l ∉ lowCols F at hl; simp [lowCols] at hl; omega)
      (total F cside fun h => (sixSides h).2) (fun p => (degreeBalance F p).1)
      (fun l p hl => by simpa [Nat.add_comm] using disjointDegrees F (mem_filter.mp hl).2)
      (by intro l p; simp [lines,points]) planeFacts.2.1 planeFacts.1 planeFacts.2.2.2 uniqueness.2 throughOnly.2

#print axioms disjointDegrees
#print axioms tenLowLabels

end Checkpoint139
