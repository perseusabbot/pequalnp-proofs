import PlaneTwo

namespace Checkpoint133.Plane
open Finset

def orbit (b : Box) := univ.image (fun q : H => turn q b)
def FamilyCovers (s : Finset Box) := ∀ i j,zeroCell i j → ∃ b∈s,i∈b.1 ∧ j∈b.2
def Stable (s : Finset Box) := ∀ b∈s,∀ q : H,turn q b∈s

theorem turnZero (b : Box) : turn 0 b=b := by
  apply Prod.ext <;> ext v <;> simp [turn,moveZero]
theorem turnTurn (p q : H) (b : Box) : turn p (turn q b)=turn (q+p) b := by
  apply Prod.ext <;> ext v <;> simp [turn,moveAdd]

theorem stableFromSingleRotation {s : Finset Box}
    (step : ∀ b∈s, turn 1 b∈s) : Stable s := by
  intro b hb q
  have repeatTurn (n : ℕ) : turn (n • (1 : H)) b ∈ s := by
    induction n with
    | zero => simpa only [zero_nsmul,turnZero] using hb
    | succ m ih => simpa only [succ_nsmul,turnTurn] using step _ ih
  have rep : ∀ h : H, h.val • (1 : H) = h := by decide +kernel
  simpa only [rep] using repeatTurn q.val

theorem onDeskBoard : ∀ i j, zeroCell i j ↔ (lines.getD i.val 0).testBit j.val = false := by
  intro i
  fin_cases i <;> decide +kernel

theorem hitsLine : ∀ i j : V,∃ q : H,¬zeroCell (move q i) j := by
  intro i
  fin_cases i <;> decide +kernel
theorem multiples : ∀ k : H,k≠0 → ∀ h : H,∃ m : Fin 7,m.val • k=h := by decide +kernel

theorem cardOrbit {b : Box} (g : Good b) (rows : b.1.Nonempty) (cols : b.2.Nonempty) : (orbit b).card=7 := by
  have inj : Function.Injective (fun q : H => turn q b) := by
    intro p q same
    by_contra different
    let k := p-q
    have nk : k≠0 := sub_ne_zero.mpr different
    have fixed : turn k b=b := by
      have e := congrArg (turn (-q)) same
      simpa only [turnTurn,k,sub_eq_add_neg,add_neg_cancel,turnZero] using e
    have rep (m : ℕ) : turn (m • k) b=b := by
      induction m with
      | zero => simp [turnZero]
      | succ m ih => rw [succ_nsmul,←turnTurn,ih,fixed]
    obtain ⟨i,hi⟩ := rows
    obtain ⟨j,hj⟩ := cols
    obtain ⟨h,bad⟩ := hitsLine i j
    obtain ⟨m,hm⟩ := multiples k nk h
    have fixedH : turn h b=b := hm ▸ rep m.val
    exact bad (g _ ((memLeft h b i).mp (by simpa only [fixedH] using hi)) j hj)
  simp [orbit,card_image_of_injective _ inj]

theorem separate {a b : Box} {i j : V} (inRow : i∈a.1) (inCol : j∈a.2) (outside : ¬Covers b i j) : Disjoint (orbit a) (orbit b) := by
  apply disjoint_left.mpr
  intro c ha hb
  obtain ⟨p,_,pa⟩ := mem_image.mp ha
  obtain ⟨q,_,qb⟩ := mem_image.mp hb
  have present : Covers a i j := ⟨0,by simpa only [moveZero] using inRow,by simpa only [moveZero] using inCol⟩
  have inC : Covers c i j := pa ▸ (turnCover p a i j).mpr present
  exact outside ((turnCover q b i j).mp (qb.symm ▸ inC))

theorem stableMinimum {s : Finset Box} (good : ∀ b∈s,Good b) (covers : FamilyCovers s) (stable : Stable s) : 21≤s.card := by
  obtain ⟨a,ha,ra,ca⟩ := covers 0 1 (by decide +kernel)
  have gap (a b : Box) (ga : Good a) (gb : Good b) : ∃ i j,zeroCell i j ∧ ¬Covers a i j ∧ ¬Covers b i j := by
    have h := twoOrbits a b ga gb
    unfold PairCovers at h
    push Not at h
    exact h
  obtain ⟨i,j,z,oa,_⟩ := gap a a (good a ha) (good a ha)
  obtain ⟨b,hb,rb,cb⟩ := covers i j z
  have ba := separate rb cb oa
  obtain ⟨i',j',z',oaa,obb⟩ := gap a b (good a ha) (good b hb)
  obtain ⟨c,hc,rc,cc⟩ := covers i' j' z'
  have ca' := separate rc cc oaa
  have cb' := separate rc cc obb
  have inside {w} (hw : w∈s) : orbit w⊆s := by
    intro u hu
    obtain ⟨q,_,rfl⟩ := mem_image.mp hu
    exact stable w hw q
  have low := card_le_card (union_subset (inside hc) (union_subset (inside hb) (inside ha)))
  rw [card_union_of_disjoint (disjoint_union_right.mpr ⟨cb',ca'⟩),card_union_of_disjoint ba,
      cardOrbit (good c hc) ⟨_,rc⟩ ⟨_,cc⟩,cardOrbit (good b hb) ⟨_,rb⟩ ⟨_,cb⟩,cardOrbit (good a ha) ⟨_,ra⟩ ⟨_,ca⟩] at low
  exact low

def strip (i : V) : Box := ({i},univ.filter fun j => zeroCell i j)
theorem stripBound : ∃ s : Finset Box,s.card=21 ∧ (∀ b∈s,Good b) ∧ FamilyCovers s ∧ Stable s := by
  let s := univ.image strip
  have good : ∀ b∈s,Good b := by
    intro b hb
    obtain ⟨i,_,rfl⟩ := mem_image.mp hb
    intro x hx y hy
    obtain rfl : x=i := mem_singleton.mp hx
    exact (mem_filter.mp hy).2
  have covers : FamilyCovers s := fun i j z => ⟨strip i,mem_image_of_mem _ (mem_univ _),mem_singleton_self _,mem_filter.mpr ⟨mem_univ _,z⟩⟩
  have stable : Stable s := by
    intro b hb q
    obtain ⟨i,_,rfl⟩ := mem_image.mp hb
    have inverse (v : V) : move (-q) (move q v)=v := by simp only [moveAdd,neg_add_cancel,moveZero]
    let a := move (-q) i
    have f : move q a=i := by simp only [a,moveAdd,add_neg_cancel,moveZero]
    have eq : turn q (strip i)=strip a := by
      apply Prod.ext
      · ext v
        simp only [memLeft,strip,mem_singleton]
        exact ⟨fun h => (inverse v).symm.trans (congrArg (move (-q)) h),fun h => h ▸ f⟩
      · ext v
        simp only [memRight,strip,mem_filter,mem_univ,true_and]
        simpa only [f] using periodic q a v
    exact eq ▸ mem_image_of_mem _ (mem_univ _)
  refine ⟨s,le_antisymm ?_ (stableMinimum good covers stable),good,covers,stable⟩
  exact (card_image_le.trans_eq (show (univ : Finset V).card=21 by decide))

/-- The desk uses a list of rectangles. Duplicates cannot reduce the lower bound. -/
theorem deskListBound (L : List Box)
    (good : ∀ b∈L, ∀ i∈b.1, ∀ j∈b.2, (lines.getD i.val 0).testBit j.val = false)
    (cover : ∀ i j : V, (lines.getD i.val 0).testBit j.val = false → ∃ b∈L, i∈b.1 ∧ j∈b.2)
    (rotated : ∀ b∈L, turn 1 b∈L) : 21 ≤ L.length := by
  have g : ∀ b∈L.toFinset, Good b := by
    intro b hb i hi j hj
    exact (onDeskBoard i j).mpr (good b (List.mem_toFinset.mp hb) i hi j hj)
  have c : FamilyCovers L.toFinset := by
    intro i j z
    obtain ⟨b,hb,hi,hj⟩ := cover i j ((onDeskBoard i j).mp z)
    exact ⟨b,List.mem_toFinset.mpr hb,hi,hj⟩
  have r : Stable L.toFinset := stableFromSingleRotation fun b hb =>
    List.mem_toFinset.mpr (rotated b (List.mem_toFinset.mp hb))
  exact (stableMinimum g c r).trans (List.toFinset_card_le _)

def turnFamily (q : H) (s : Finset Box) := s.image (turn q)
theorem turnFamilyZero (s : Finset Box) : turnFamily 0 s = s := by
  have eq : turn 0 = id := funext turnZero
  simp [turnFamily,eq]
theorem turnFamilyAdd (p q : H) (s : Finset Box) :
    turnFamily p (turnFamily q s) = turnFamily (q+p) s := by
  simp [turnFamily,Finset.image_image,turnTurn,Function.comp_def]

/-- Every full cover with at most twenty rectangles has seven distinct translates. -/
theorem smallCoverOrbit {s : Finset Box} (good : ∀ b∈s, Good b) (covers : FamilyCovers s)
    (small : s.card < 21) : ((univ : Finset H).image (fun q => turnFamily q s)).card = 7 := by
  have inj : Function.Injective (fun q : H => turnFamily q s) := by
    intro p q same
    by_contra ne
    let k := p-q
    have nk : k≠0 := sub_ne_zero.mpr ne
    have fixed : turnFamily k s=s := by
      have e := congrArg (turnFamily (-q)) same
      simpa only [turnFamilyAdd,k,sub_eq_add_neg,add_neg_cancel,turnFamilyZero] using e
    have iterated (n : ℕ) : turnFamily (n • k) s = s := by
      induction n with
      | zero => simp [turnFamilyZero]
      | succ n ih => rw [succ_nsmul,←turnFamilyAdd,ih,fixed]
    have stable : Stable s := by
      intro b hb h
      obtain ⟨n,hn⟩ := multiples k nk h
      have fixH : turnFamily h s=s := hn ▸ iterated n.val
      have t : turn h b ∈ turnFamily h s := mem_image_of_mem _ hb
      rwa [fixH] at t
    exact (Nat.not_le_of_lt small) (stableMinimum good covers stable)
  simp [card_image_of_injective _ inj]

#print axioms smallCoverOrbit
#print axioms deskListBound
#print axioms cardOrbit
#print axioms stableMinimum
#print axioms stripBound
end Checkpoint133.Plane
