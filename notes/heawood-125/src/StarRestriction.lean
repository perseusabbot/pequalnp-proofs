import MissingStar
import BottomPairs

namespace Checkpoint123.Heawood
open Finset SimpleGraph StarUnion
open Checkpoint122.Pruning
open Checkpoint121.Heawood (neighborhood PairedBottom optimalBottom)
open PEqualNP.Outside.L_meta_2268_aux.Normal
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- The four terminals remaining when all vertices outside a missing star are set to zero. -/
def terminals (v : V) := insert v (neighborhood v)

theorem threeNeighbors : ∀ v, (neighborhood v).card = 3 := by decide +kernel
theorem fourTerminals : ∀ v, (terminals v).card = 4 := by decide +kernel
private theorem thinOther : ∀ v c : V, c ≠ v → ((neighborhood c) ∩ terminals v).card ≤ 1 := by
  decide +kernel
attribute [local instance 2000] Finset.decidableDforallFinset
private theorem separate : ∀ v : V, ∀ a ∈ neighborhood v, ∀ b ∈ neighborhood v, ¬ G.Adj a b := by
  decide +kernel
private theorem inside (v a b : V) (ha : a ∈ terminals v) (hb : b ∈ terminals v) (adj : G.Adj a b) :
    s(a,b) ∈ star v := by
  rcases mem_insert.mp ha with rfl|pa
  · exact mem_image.mpr ⟨b,List.mem_toFinset.mpr adj,rfl⟩
  rcases mem_insert.mp hb with rfl|pb
  · exact mem_image.mpr ⟨a,List.mem_toFinset.mpr adj.symm,Sym2.eq_swap⟩
  · exact False.elim (separate v a pa b pb adj)

/-- The surviving products are false everywhere on this four-variable restriction. -/
theorem deadOnStar {w : Wire 14} (sound : ∀ z, accepts w z → predicate z) {v : V}
    (lost : G.edgeFinset \ survivors w = star v) (p : Product 14) (hp : p ∈ w.jobs)
    {z : V → Bool} (localInput : ∀ x, z x=true → x ∈ terminals v) :
    ¬(lit p.1 z ∧ lit p.2 z) := by
  rintro ⟨⟨a,ha,za⟩,⟨b,hb,zb⟩⟩
  have adj := (describe sound).2 p hp a ha b hb
  have miss := inside v a b (localInput a za) (localInput b zb) adj
  rw [← lost] at miss
  exact (mem_sdiff.mp miss).2 ((in_survivors w _).mpr ⟨p,hp,a,ha,b,hb,rfl⟩)

private def addStar (v : V) (J : Finset (Product 14)) := insert ({v},neighborhood v) J

private theorem completedTruth {w : Wire 14} (sound : ∀ z, accepts w z → predicate z) {v : V}
    (lost : G.edgeFinset \ survivors w = star v) (z : V → Bool) :
    (∃ p ∈ addStar v w.jobs, lit p.1 z ∧ lit p.2 z) ↔ predicate z := by
  constructor
  · rintro ⟨p,hp,ha,hb⟩
    rcases mem_insert.mp hp with rfl | h
    · obtain ⟨a,ha,za⟩ := ha
      obtain ⟨b,hb,zb⟩ := hb
      have eq : a=v := mem_singleton.mp ha
      subst a
      exact (orientation z).mpr ⟨v,b,List.mem_toFinset.mp hb,za,zb⟩
    · exact sound z (Or.inr ⟨p,h,ha,hb⟩)
  · intro hz
    obtain ⟨a,b,adj,za,zb⟩ := (orientation z).mp hz
    by_cases h : s(a,b) ∈ survivors w
    · obtain ⟨p,hp,i,hi,j,hj,e⟩ := (in_survivors w _).mp h
      rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨p,mem_insert_of_mem hp,⟨_,hi,za⟩,⟨_,hj,zb⟩⟩
      · exact ⟨p,mem_insert_of_mem hp,⟨_,hi,zb⟩,⟨_,hj,za⟩⟩
    · have miss : s(a,b) ∈ star v := lost ▸ mem_sdiff.mpr ⟨by simpa using adj,h⟩
      obtain ⟨u,hu,eq⟩ := mem_image.mp miss
      refine ⟨({v},neighborhood v),mem_insert_self ..,?_⟩
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨⟨_,mem_singleton_self _,za⟩,⟨_,hu,zb⟩⟩
      · exact ⟨⟨_,mem_singleton_self _,zb⟩,⟨_,hu,za⟩⟩

/-- Adding any missing neighbor pair and its triple yields an optimal staged library. -/
theorem completeBottom {w : Wire 14} (B : List (Support 14)) (built : Built B)
    (ready : ∀ p ∈ w.jobs, Ready B p.1 ∧ Ready B p.2)
    (sound : ∀ z, accepts w z → predicate z) {v : V} (lost : G.edgeFinset \ survivors w = star v)
    (six : w.jobs.card=6) (twelve : B.length=12) {t : V} (ht : t ∈ neighborhood v) :
    PairedBottom (neighborhood v :: (neighborhood v).erase t :: B) := by
  classical
  let J := addStar v w.jobs
  let A := (neighborhood v).erase t
  let L := neighborhood v :: A :: B
  have pairCard : A.card=2 := by rw [show A=(neighborhood v).erase t from rfl,card_erase_of_mem ht,threeNeighbors]
  obtain ⟨a,b,_,ab⟩ := card_eq_two.mp pairCard
  have pairOK : Built (A::B) := ⟨built,{a},{b},by simp [ab],Or.inl (by simp),Or.inl (by simp)⟩
  have topOK : Built L := ⟨pairOK,{t},A,by simpa [A] using (insert_erase ht).symm,
    Or.inl (by simp),Or.inr (List.mem_cons_self ..)⟩
  let f (i : Fin J.card) : Product 14 := (J.equivFin.symm i).val
  have mem (i) : f i ∈ J := (J.equivFin.symm i).property
  have lift {U} (h : Ready B U) : Ready L U :=
    h.imp_right (fun x => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ x))
  have rdy (p : Product 14) (hp : p ∈ J) : Ready L p.1 ∧ Ready L p.2 := by
    rcases mem_insert.mp hp with rfl|old
    · exact ⟨Or.inl (by simp),Or.inr (List.mem_cons_self ..)⟩
    · exact ⟨lift (ready _ old).1,lift (ready _ old).2⟩
  have truth (z) : coverTruth (fun i => (f i).1) (fun i => (f i).2) z ↔ predicate z := by
    refine Iff.trans ?_ (completedTruth sound lost z)
    constructor
    · rintro ⟨i,ha,hb⟩
      exact ⟨f i,mem i,ha,hb⟩
    · rintro ⟨p,hp,ha,hb⟩
      refine ⟨J.equivFin ⟨p,hp⟩,?_⟩
      simpa [f,lit] using And.intro ha hb
  have size : J.card ≤ 7 := (card_insert_le ..).trans (by rw [six])
  apply optimalBottom L (fun i => (f i).1) (fun i => (f i).2) topOK (fun i => rdy _ (mem i)) truth
  simp only [L,List.length_cons,twelve]
  omega

/-- Each pre-existing bottom gate sees at most one of the four terminals on the missing star. -/
theorem bottomThin {w : Wire 14} (B : List (Support 14)) (built : Built B)
    (ready : ∀ p ∈ w.jobs, Ready B p.1 ∧ Ready B p.2)
    (sound : ∀ z, accepts w z → predicate z) {v : V} (lost : G.edgeFinset \ survivors w = star v)
    (six : w.jobs.card=6) (twelve : B.length=12) (S : Support 14) (memS : S ∈ B) :
    (S ∩ terminals v).card ≤ 1 := by
  classical
  have augmented := fun t (ht : t ∈ neighborhood v) => completeBottom B built ready sound lost six twelve ht
  obtain ⟨t,ht⟩ : (neighborhood v).Nonempty := card_pos.mp (by rw [threeNeighbors]; decide)
  obtain ⟨C,_,F,hF,_,lib⟩ := augmented t ht
  have listed : S ∈ (univ.image (fun c : C => neighborhood c)) ∪ (univ.image F) := by
    rw [← lib]
    exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ memS))
  have own : ∃ c : V, S ⊆ neighborhood c ∧ (S.card=2 ∨ S.card=3) := by
    rcases mem_union.mp listed with h|h <;> obtain ⟨c,_,rfl⟩ := mem_image.mp h
    · exact ⟨c,Subset.rfl,Or.inr (threeNeighbors _)⟩
    · exact ⟨c,(hF c).1,Or.inl (hF c).2⟩
  obtain ⟨c,sub,sz⟩ := own
  by_cases same : c=v
  · subst c
    exfalso
    have absent (x) (hx : x ∈ neighborhood v) :
        neighborhood v ∉ B ∧ (neighborhood v).erase x ∉ B := by
      obtain ⟨_,_,_,_,nd,_⟩ := augmented x hx
      have h := List.nodup_cons.mp nd
      exact ⟨fun k => h.1 (List.mem_cons_of_mem _ k),(List.nodup_cons.mp h.2).1⟩
    rcases sz with two|three
    · have left : (neighborhood v \ S).Nonempty := card_pos.mp (by rw [card_sdiff_of_subset sub,threeNeighbors,two]; decide)
      obtain ⟨x,hx⟩ := left
      obtain ⟨hn,hs⟩ := mem_sdiff.mp hx
      have part : S ⊆ (neighborhood v).erase x := fun u hu => mem_erase.mpr ⟨fun eq => hs (eq ▸ hu),sub hu⟩
      have eq := eq_of_subset_of_card_le part (by rw [card_erase_of_mem hn,threeNeighbors,two])
      exact (absent x hn).2 (eq ▸ memS)
    · have eq := eq_of_subset_of_card_le sub (by rw [threeNeighbors,three])
      exact (absent t ht).1 (eq ▸ memS)
  · exact (card_le_card (show S ∩ terminals v ⊆ neighborhood c ∩ terminals v from fun _ hu => mem_inter.mpr ⟨sub (mem_inter.mp hu).1,(mem_inter.mp hu).2⟩)).trans (thinOther v c same)

#print axioms completeBottom
#print axioms bottomThin
#print axioms deadOnStar
end Checkpoint123.Heawood
