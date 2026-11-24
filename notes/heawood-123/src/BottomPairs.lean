import OptimalStars

namespace Checkpoint121.Heawood
open Finset SimpleGraph StarUnion
open PEqualNP.Outside.L_meta_3004_aux.Controls
open PEqualNP.Outside.L_meta_2268_aux.Normal

def neighborhood (v : V) := (nbr v).toFinset
private theorem triple : ∀ v, (neighborhood v).card = 3 := by decide +kernel
private theorem overlap : ∀ u v, u ≠ v → ((neighborhood u) ∩ (neighborhood v)).card ≤ 1 := by
  set_option maxRecDepth 10000 in decide +kernel

private theorem owner {u v : V} {T : Finset V} (pair : 2 ≤ T.card)
    (a : T ⊆ neighborhood u) (b : T ⊆ neighborhood v) : u = v := by
  by_contra h
  have lo := card_le_card (subset_inter a b)
  have hi := overlap u v h
  omega

private theorem pairBelow (B : List (Finset V)) (ok : Built B) (S : Finset V)
    (ready : Ready B S) (large : 2 ≤ S.card) :
    ∃ T ∈ B, T ⊆ S ∧ T.card = 2 := by
  induction B generalizing S with
  | nil => rcases ready with small | mem; omega; simp at mem
  | cons a B ih =>
    obtain ⟨legal,b,c,join,rb,rc⟩ := ok
    rcases ready with small | mem
    · omega
    rcases List.mem_cons.mp mem with rfl | tail
    · by_cases exactTwo : S.card = 2
      · exact ⟨S,List.mem_cons_self ..,Subset.rfl,exactTwo⟩
      have hb : b ⊆ S := join ▸ subset_union_left
      have hc : c ⊆ S := join ▸ subset_union_right
      have cost : S.card ≤ b.card+c.card := join ▸ card_union_le ..
      have step (U : Finset V) (sub : U ⊆ S) (r : Ready B U) (two : 2 ≤ U.card) :
          ∃ T ∈ S::B, T ⊆ S ∧ T.card = 2 := by
        obtain ⟨T,hT,hs,sz⟩ := ih legal U r two
        exact (show ∃ T ∈ S::B, T ⊆ S ∧ T.card = 2 from
          ⟨T,List.mem_cons_of_mem _ hT,hs.trans sub,sz⟩)
      by_cases two : 2 ≤ b.card
      · exact step b hb rb two
      · exact step c hc rc (by omega)
    · obtain ⟨T,hT,hs,sz⟩ := ih legal S (Or.inr tail) large
      exact ⟨T,List.mem_cons_of_mem _ hT,hs,sz⟩

private theorem factors {a b : ℕ} (h : a*b=3) : a=1 ∧ b=3 ∨ a=3 ∧ b=1 := by
  have ha := (Nat.dvd_prime Nat.prime_three).mp (show a ∣ 3 from ⟨b,h.symm⟩)
  rcases ha with rfl | rfl
  · exact Or.inl ⟨rfl,by simpa using h⟩
  · exact Or.inr ⟨rfl,by omega⟩

/-- Each optimum has seven distinct triples and exactly one private pair inside each triple. -/
def PairedBottom (B : List (Finset V)) : Prop :=
  ∃ C : Finset V, (C = points ∨ C = lines) ∧ ∃ F : C → Finset V,
    (∀ c, F c ⊆ neighborhood c ∧ (F c).card = 2) ∧ B.Nodup ∧
      B.toFinset = (univ.image (fun c : C => neighborhood c)) ∪ (univ.image F)

theorem optimalBottom {m : ℕ} (B : List (Finset V)) (X Y : Fin m → Finset V)
    (built : Built B) (ready : ∀ i, Ready B (X i) ∧ Ready B (Y i))
    (truth : ∀ z, coverTruth X Y z ↔ predicate z) (cost : B.length+2*m ≤ 28) : PairedBottom B := by
  classical
  obtain ⟨_,len,cnt,cls⟩ := optimalProducts B X Y built ready truth cost
  let C := univ.biUnion (fun i => if (X i).card ≤ 1 then X i else Y i)
  change C=points ∨ C=lines at cls
  have sizes : points.card=7 ∧ lines.card=7 := by decide +kernel
  have cardC : C.card=7 := cls.elim (fun h => h ▸ sizes.1) (fun h => h ▸ sizes.2)
  obtain ⟨clean,_⟩ := cleanCoverOfSemantics G X Y (fun z => (truth z).trans (orientation z))
  have roots (c : C) : Ready B (neighborhood c) := by
    obtain ⟨i,_,hm⟩ := mem_biUnion.mp c.property
    rcases factors (cnt i) with ⟨a,b⟩ | ⟨a,b⟩
    · have mem : c.val ∈ X i := by simpa [a] using hm
      have sub : Y i ⊆ neighborhood c := fun v hv => List.mem_toFinset.mpr (clean i c mem v hv)
      have eq := eq_of_subset_of_card_le sub (by rw [triple,b])
      exact eq ▸ (ready i).2
    · have mem : c.val ∈ Y i := by simpa [a] using hm
      have sub : X i ⊆ neighborhood c := fun v hv => List.mem_toFinset.mpr (clean i v hv c mem).symm
      have eq := eq_of_subset_of_card_le sub (by rw [triple,a])
      exact eq ▸ (ready i).1
  have choice (c : C) := pairBelow B built (neighborhood c) (roots c) (by rw [triple]; decide)
  choose F hF using choice
  let N (c : C) := neighborhood c
  have hN (c : C) : (N c).card = 3 := triple c
  have fmem (c : C) : N c ∈ B := (roots c).resolve_left (by have := triple c; omega)
  have injN : Function.Injective N := by
    intro c d same
    apply Subtype.ext
    exact owner (T := N c) (by rw [hN]; decide) Subset.rfl (subset_of_eq same)
  have injF : Function.Injective F := by
    intro c d same
    apply Subtype.ext
    exact owner (T := F c) (by rw [(hF c).2.2]) (hF c).2.1 (same ▸ (hF d).2.1)
  have sep : Disjoint (univ.image N) (univ.image F) := by
    apply Finset.disjoint_left.mpr
    rintro T ht hf
    obtain ⟨c,_,rfl⟩ := mem_image.mp ht
    obtain ⟨d,_,h⟩ := mem_image.mp hf
    have eq := congrArg Finset.card h
    have three := hN c
    have two := (hF d).2.2
    omega
  let all := univ.image N ∪ univ.image F
  have total : all.card=14 := by
    change (univ.image N ∪ univ.image F).card=14
    rw [card_union_of_disjoint sep,card_image_of_injective _ injN,card_image_of_injective _ injF]
    simp only [card_univ,Fintype.card_coe,cardC]
  have sub : all ⊆ B.toFinset := by
    intro T ht
    apply List.mem_toFinset.mpr
    rcases mem_union.mp ht with hn | hp
    · obtain ⟨c,_,rfl⟩ := mem_image.mp hn
      exact fmem c
    · obtain ⟨c,_,rfl⟩ := mem_image.mp hp
      exact (hF c).1
  have cap := B.toFinset_card_le
  have eq := eq_of_subset_of_card_le sub (by omega)
  have tally := congrArg Finset.card eq
  have nd : B.Nodup := by
    apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (B : Multiset (Finset V)))).mp
    change B.toFinset.card=B.length
    omega
  exact ⟨C,cls,F,fun c => (hF c).2,nd,eq.symm⟩

/-- The support of each physical bottom OR is accounted for by the pairs and triples. -/
theorem physicalBottom (bot mid top : List Stage.Port) (out : ℕ)
    (valid : ∀ p ∈ mid, p.1 < 14+bot.length ∧ p.2 < 14+bot.length)
    (computes : ∀ z, PEqualNP.MetaComplexity.circuitFun 14 (Stage.circuit 14 bot mid top out) z = true ↔ predicate z)
    (size : (Stage.circuit 14 bot mid top out).size ≤ 27) : PairedBottom (Stage.sched 14 bot) := by
  classical
  obtain ⟨bsize,msize,_,reaches⟩ := physicalCounts bot mid top out valid computes size
  let S := (Stage.sourceWires mid.length top).getD out ∅
  let X (i : Fin mid.length) := (Stage.sourceWires 14 bot).getD (mid[i].1) ∅
  let Y (i : Fin mid.length) := (Stage.sourceWires 14 bot).getD (mid[i].2) ∅
  have all : S=univ := eq_of_subset_of_card_le (subset_univ _) (by simpa [S] using reaches.ge)
  have y (z) : coverTruth X Y z ↔ predicate z := by
    have h : reachableTruth S X Y z ↔ predicate z :=
      (Stage.physicalTruth 14 bot mid top out valid z).symm.trans (computes z)
    rw [all] at h
    simpa [reachableTruth,coverTruth] using h
  exact optimalBottom _ X Y (Stage.scheduled 14 bot).1
    (fun _ => ⟨(Stage.scheduled 14 bot).2 _,(Stage.scheduled 14 bot).2 _⟩) y
    (by simp [Stage.sched,Stage.supportLength,bsize,msize])

#print axioms physicalBottom

#print axioms optimalBottom
end Checkpoint121.Heawood
