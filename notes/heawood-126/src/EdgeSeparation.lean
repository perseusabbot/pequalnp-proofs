import RegularBottom

namespace Checkpoint124.Heawood
open Finset SimpleGraph Checkpoint122.Pruning
open PEqualNP.Outside.L_meta_3004_aux.Controls

def endpoint (i : Fin 21) (side : Bool) : V :=
  let p := edges.getD i.val (0,0)
  Fin.ofNat 14 (if side then p.2 else p.1)
def edge (i : Fin 21) : Sym2 V := s(endpoint i false,endpoint i true)
theorem indexedEdges : univ.image edge = G.edgeFinset := by decide +kernel
theorem indexedAdj : ∀ i, G.Adj (endpoint i false) (endpoint i true) := by decide +kernel

private def test (i : Fin 21) := pair (endpoint i false) (endpoint i true)
private def witness (i j : Fin 21) : V × V :=
  let a := endpoint i false
  let b := endpoint i true
  let c := endpoint j false
  let d := endpoint j true
  if a=c then (a,a) else if b=d then (b,b) else if G.Adj a d then (c,b) else (a,d)

private def usable (i j : Fin 21) (c u : V) : Prop :=
  G.Adj c u ∧ s(c,u)≠edge i ∧ s(c,u)≠edge j
private instance {i j c u} : Decidable (usable i j c u) := by unfold usable; infer_instance

/-- For each pair of different lost edges, the designated nonedge meets every
regular support which hits both positive assignments. -/
private theorem table : ∀ i j : Fin 21, i≠j →
    let w := witness i j
    ¬G.Adj w.1 w.2 ∧ ∀ k l : Bool,
      let a := endpoint i k
      let b := endpoint j l
      (a=b ∨ ∃ c, usable i j c a ∧ usable i j c b) →
        a=w.1 ∨ a=w.2 ∨ b=w.1 ∨ b=w.2 := by
  set_option maxRecDepth 15000 in
  set_option maxHeartbeats 0 in
  decide +kernel

private theorem pairTruth (u v : V) : predicate (pair u v) ↔ G.Adj u v := by
  rw [orientation]
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    simp only [pair,decide_eq_true_eq] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · exact False.elim (h.ne rfl)
    · exact h
    · exact h.symm
    · exact False.elim (h.ne rfl)
  · exact fun h => ⟨u,v,h,by simp [pair],by simp [pair]⟩

private theorem touches {S : Support 14} {i} (hit : lit S (test i)) :
    ∃ k : Bool, endpoint i k∈S := by
  obtain ⟨a,ha,on⟩ := hit
  rcases (show a=endpoint i false ∨ a=endpoint i true by simpa [test,pair] using on) with rfl|rfl
  · exact ⟨false,ha⟩
  · exact ⟨true,ha⟩

theorem separatingInput {H : Finset (Sym2 V)} (sub : H⊆G.edgeFinset) {i j : Fin 21}
    (ne : i≠j) (hi : edge i∉H) (hj : edge j∉H) :
    ∃ z, ¬predicate z ∧ ∀ S, Regular H S → lit S (test i) → lit S (test j) → lit S z := by
  let w := witness i j
  obtain ⟨off,rules⟩ := table i j ne
  refine ⟨pair w.1 w.2,fun yes => off ((pairTruth ..).mp yes),?_⟩
  intro S reg hitI hitJ
  obtain ⟨k,hk⟩ := touches hitI
  obtain ⟨l,hl⟩ := touches hitJ
  have retained {c u} (h : s(c,u)∈H) : usable i j c u :=
    ⟨by simpa using sub h,fun eq => hi (eq ▸ h),fun eq => hj (eq ▸ h)⟩
  have co : endpoint i k=endpoint j l ∨ ∃ c, usable i j c (endpoint i k) ∧ usable i j c (endpoint j l) := by
    rcases reg with tiny|⟨c,adj⟩
    · exact Or.inl (card_le_one.mp tiny _ hk _ hl)
    · exact Or.inr ⟨c,retained (adj _ hk),retained (adj _ hl)⟩
  rcases rules k l co with a|a|b|b
  · exact ⟨_,hk,by simp [pair,w,a]⟩
  · exact ⟨_,hk,by simp [pair,w,a]⟩
  · exact ⟨_,hl,by simp [pair,w,b]⟩
  · exact ⟨_,hl,by simp [pair,w,b]⟩

/-- A disjunction of conjunctions of regular signals can restore at most one
lost edge per conjunction, because every negative graph input remains available. -/
theorem restorationBound (w : Wire 14) (sub : survivors w⊆G.edgeFinset)
    (sound : ∀ z, accepts w z → predicate z) (features : ℕ → Support 14)
    (regular : ∀ a, Regular (survivors w) (features a)) (terms : List (Finset ℕ))
    (truth : ∀ z, ¬accepts w z → (predicate z ↔ ∃ t∈terms, ∀ a∈t, lit (features a) z)) :
    missed w ≤ terms.length := by
  classical
  let L := G.edgeFinset \ survivors w
  have chooseIndex (e : L) : ∃ i, edge i=e.val := by
    have h := (mem_sdiff.mp e.property).1
    rw [← indexedEdges] at h
    obtain ⟨i,_,eq⟩ := mem_image.mp h
    exact ⟨i,eq⟩
  choose index idx using chooseIndex
  have gone (e : L) : edge (index e)∉survivors w := idx e ▸ (mem_sdiff.mp e.property).2
  have quiet (e : L) : ¬accepts w (test (index e)) :=
    fun h => gone e ((survives_iff sound ..).mpr h)
  have chooseTerm (e : L) : ∃ t∈terms, ∀ a∈t, lit (features a) (test (index e)) :=
    (truth _ (quiet e)).mp ((pairTruth ..).mpr (indexedAdj _))
  choose term member all using chooseTerm
  let target (e : L) : terms.toFinset := ⟨term e,List.mem_toFinset.mpr (member e)⟩
  have one : Function.Injective target := by
    intro e f eq
    by_contra diff
    have ne : index e≠index f := fun h => diff (Subtype.ext ((idx e).symm.trans ((congrArg edge h).trans (idx f))))
    obtain ⟨z,off,hits⟩ := separatingInput sub ne (gone e) (gone f)
    have same : term e=term f := congrArg Subtype.val eq
    apply off
    exact (truth z (fun h => off (sound z h))).mpr
      ⟨term e,member e,fun a ha => hits _ (regular a) (all e a ha) (all f a (same ▸ ha))⟩
  have count := Fintype.card_le_of_injective target one
  simp only [Fintype.card_coe] at count
  exact count.trans terms.toFinset_card_le

#print axioms separatingInput
#print axioms restorationBound
end Checkpoint124.Heawood
