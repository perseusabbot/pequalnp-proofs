import HeawoodStages
import Sharp

namespace Checkpoint121.Heawood
open Finset SimpleGraph StarUnion
open PEqualNP.Outside.L_meta_3004_aux.Controls
open PEqualNP.Outside.L_meta_2268_aux.Normal

def points : Finset V := univ.filter (fun v => v.val < 7)
def lines : Finset V := univ.filter (fun v => 7 ≤ v.val)
def left (i : Fin 7) : V := Fin.castAdd 7 i
def right : Fin 7 → V := ![7,9,8,12,13,10,11]
def block : V → Fin 7 := ![0,1,2,3,4,5,6,0,2,1,5,6,3,4]
def pick (b : Fin 7 → Bool) (i : Fin 7) := if b i then left i else right i
def chosen (b : Fin 7 → Bool) := (univ : Finset (Fin 7)).image (pick b)
private theorem pairs : ∀ i, G.Adj (left i) (right i) := by decide +kernel
private theorem labels : ∀ i, block (left i) = i ∧ block (right i) = i := by decide +kernel

/-- Seven matching edges leave just 128 candidates for a seven-vertex cover. -/
private theorem options : ∀ b : Fin 7 → Bool,
    (∀ e ∈ edges, Fin.ofNat 14 e.1 ∈ chosen b ∨ Fin.ofNat 14 e.2 ∈ chosen b) →
    chosen b = points ∨ chosen b = lines := by
  set_option maxRecDepth 16000 in
  set_option maxHeartbeats 5000000 in
  decide +kernel

theorem minimumCovers (C : Finset V) (cover : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) (small : C.card ≤ 7) :
    C = points ∨ C = lines := by
  classical
  let b (i : Fin 7) := decide (left i ∈ C)
  have subset : chosen b ⊆ C := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    by_cases has : left i ∈ C
    · simp [pick,b,has]
    · simpa [pick,b,has] using (cover _ _ (pairs i)).resolve_left has
  have inv (i) : block (pick b i) = i := by
    cases h : b i <;> simp [pick,h,labels]
  have inj : Function.Injective (pick b) := fun i j h =>
    (inv i).symm.trans ((congrArg block h).trans (inv j))
  have number : (chosen b).card = 7 := by
    simp only [chosen,Finset.card_image_of_injective _ inj,card_univ,Fintype.card_fin]
  have eq : chosen b = C := eq_of_subset_of_card_le subset (by omega)
  rw [← eq]
  apply options b
  intro e he
  have legal : ∀ t ∈ edges, G.Adj (Fin.ofNat 14 t.1) (Fin.ofNat 14 t.2) := by decide +kernel
  rw [eq]
  exact cover _ _ (legal e he)

private theorem edgeCount : G.edgeFinset.card = 21 := by decide +kernel
private theorem sidesCount : points.card = 7 ∧ lines.card = 7 := by decide +kernel

/-- At cost 27, all seven product centers are on one side of the incidence graph.
Each product accounts for three edges, so every product has all three neighboring leaves. -/
theorem optimalProducts {m : ℕ} (B : List (Finset V)) (X Y : Fin m → Finset V)
    (built : Built B) (ready : ∀ i, Ready B (X i) ∧ Ready B (Y i))
    (truth : ∀ z, coverTruth X Y z ↔ predicate z)
    (cost : B.length+2*m ≤ 28) :
    m=7 ∧ B.length=14 ∧
      (∀ i, (X i).card * (Y i).card = 3) ∧
      ((univ.biUnion (fun i => if (X i).card ≤ 1 then X i else Y i)) = points ∨
       (univ.biUnion (fun i => if (X i).card ≤ 1 then X i else Y i)) = lines) := by
  classical
  obtain ⟨clean,cover⟩ := cleanCoverOfSemantics G X Y (fun z => (truth z).trans (orientation z))
  have girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length := fun v p hp => (by have := girth_six v p hp; omega)
  have square : NoSquare G := by
    intro i j a b ij ia ja ib jb
    by_contra ab
    exact noSquare G girth ia ja.symm jb ib.symm ij ab
  have eCard := rectangleEdges G square B built (univ : Finset (Fin m)) X Y
    (fun i _ => (ready i).1) (fun i _ => (ready i).2) (fun i _ => clean i) G.edgeFinset (by
      intro e he
      obtain ⟨i,u,v,hu,hv,h⟩ := cover e he
      exact ⟨i,mem_univ _,u,hu,v,hv,h⟩)
  simp only [edgeCount,card_univ,Fintype.card_fin] at eCard
  let side (i : Fin m) := if (X i).card ≤ 1 then X i else Y i
  have tiny (i) : (side i).card ≤ 1 := by
    by_cases h : (X i).card ≤ 1
    · simp [side,h]
    · obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge h)
      rw [show side i = Y i by simp [side,h]]
      exact card_le_one.mpr (fun a ha b hb => square x y a b ne
        (clean i x hx a ha) (clean i y hy a ha) (clean i x hx b hb) (clean i y hy b hb))
  let C := (univ : Finset (Fin m)).biUnion side
  have cSize : C.card ≤ m := calc
    C.card ≤ ∑ i, (side i).card := card_biUnion_le
    _ ≤ ∑ _ : Fin m, 1 := sum_le_sum (fun i _ => tiny i)
    _ = m := by simp
  have cCover (u v) (huv : G.Adj u v) : u ∈ C ∨ v ∈ C := by
    obtain ⟨i,a,b,ha,hb,e⟩ := cover s(u,v) (by simpa using huv)
    have mem : a ∈ C ∨ b ∈ C := by
      by_cases h : (X i).card ≤ 1
      · exact Or.inl (mem_biUnion.mpr ⟨i,mem_univ _,by simpa [side,h] using ha⟩)
      · exact Or.inr (mem_biUnion.mpr ⟨i,mem_univ _,by simpa [side,h] using hb⟩)
    rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact mem
    · exact mem.symm
  have le : m ≤ 7 := by omega
  have sideClass := minimumCovers C cCover (by omega)
  have size : C.card=7 := sideClass.elim (fun h => h ▸ sidesCount.1) (fun h => h ▸ sidesCount.2)
  have reg : ∀ v ∉ (∅ : Finset V), (G.neighborSet v).ncard = 3 := by
    intro v _
    rw [G.ncard_neighborSet,cubic]
  let pairsN (i : Fin m) := (X i).card * (Y i).card
  have count (i : Fin m) : pairsN i ≤ 3 :=
    (cleanProductCount G ∅ reg (by simp) girth (X i) (Y i) (clean i)).1
  let parts (i : Fin m) := ((X i) ×ˢ (Y i)).image (fun e => s(e.1,e.2))
  have inc : G.edgeFinset ⊆ univ.biUnion parts := by
    intro e he
    obtain ⟨i,u,v,hu,hv,h⟩ := cover e he
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,h.symm⟩⟩
  have sumBound : 21 ≤ ∑ i, pairsN i := calc
    21 = G.edgeFinset.card := edgeCount.symm
    _ ≤ (univ.biUnion parts).card := card_le_card inc
    _ ≤ ∑ i, (parts i).card := card_biUnion_le
    _ ≤ ∑ i, pairsN i := sum_le_sum (fun i _ => by
      simpa only [parts,pairsN,card_product] using (card_image_le (s := (X i) ×ˢ (Y i)) (f := fun e => s(e.1,e.2))))
  refine ⟨by omega,by omega,?_,sideClass⟩
  intro i
  by_contra h
  have strict : pairsN i < 3 := by change pairsN i ≠ 3 at h; have := count i; omega
  have price : (∑ j, pairsN j) < ∑ _ : Fin m, 3 :=
    sum_lt_sum (fun j _ => count j) ⟨i,mem_univ _,strict⟩
  simp at price
  omega

/-- In every physical three-stage optimum, all seven AND gates are reachable
and the two OR stages use fourteen and six gates respectively. -/
theorem physicalCounts (bot mid top : List Stage.Port) (out : ℕ)
    (valid : ∀ p ∈ mid, p.1 < 14+bot.length ∧ p.2 < 14+bot.length)
    (computes : ∀ z, PEqualNP.MetaComplexity.circuitFun 14 (Stage.circuit 14 bot mid top out) z = true ↔ predicate z)
    (size : (Stage.circuit 14 bot mid top out).size ≤ 27) :
    bot.length=14 ∧ mid.length=7 ∧ top.length=6 ∧
      ((Stage.sourceWires mid.length top).getD out ∅).card=mid.length := by
  classical
  let S := (Stage.sourceWires mid.length top).getD out ∅
  let e := S.equivFin
  let src (i : Fin S.card) : Fin mid.length := (e.symm i).val
  let X (i : Fin mid.length) := (Stage.sourceWires 14 bot).getD (mid[i].1) ∅
  let Y (i : Fin mid.length) := (Stage.sourceWires 14 bot).getD (mid[i].2) ∅
  have y (z) : coverTruth (X ∘ src) (Y ∘ src) z ↔ predicate z := by
    have reach : reachableTruth S X Y z ↔ predicate z :=
      (Stage.physicalTruth 14 bot mid top out valid z).symm.trans (computes z)
    apply Iff.trans _ reach
    constructor
    · rintro ⟨i,hu,hv⟩
      exact ⟨src i,(e.symm i).property,hu,hv⟩
    · rintro ⟨i,hi,hu,hv⟩
      let j : S := ⟨i,hi⟩
      exact ⟨e j,by simpa [Function.comp_def,src,j] using hu,
        by simpa [Function.comp_def,src,j] using hv⟩
  have leftCost : (Stage.sched 14 bot).length = bot.length := by
    simp [Stage.sched,Stage.supportLength]
  have upper : S.card ≤ mid.length := by simpa only [Fintype.card_fin] using card_le_univ S
  have lower : S.card ≤ top.length+1 := by
    have := collectorBound _ (Stage.scheduled mid.length top).1 _ ((Stage.scheduled mid.length top).2 out)
    simpa [S,Stage.sched,Stage.supportLength] using this
  rw [Stage.physicalSize] at size
  have data := optimalProducts (Stage.sched 14 bot) (X ∘ src) (Y ∘ src) (Stage.scheduled 14 bot).1
    (fun _ => ⟨(Stage.scheduled 14 bot).2 _,(Stage.scheduled 14 bot).2 _⟩) y (by omega)
  obtain ⟨seven,fourteen,_⟩ := data
  change _ ∧ _ ∧ _ ∧ S.card=mid.length
  omega

#print axioms physicalCounts
#print axioms minimumCovers
#print axioms optimalProducts
end Checkpoint121.Heawood
