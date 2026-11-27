import FourCells

namespace Checkpoint138

open PEqualNP.Outside.L_meta_9338 Finset

abbrev inBox (x : Cell) (b : Box) := x.1 ∈ b.1 ∧ x.2 ∈ b.2

/-- The zero cells still needing a replacement after removing one rectangle. -/
def needsRepair (F : Finset Box) (b : Box) : Finset Cell :=
  univ.filter (fun x => bit x.1 x.2 = false ∧ ¬ ∃ c ∈ F.erase b, inBox x c)

def replaces (F : Finset Box) (b : Box) (h : H) :=
  ∀ x : Cell, bit x.1 x.2 = false → (∃ c ∈ F.erase b, inBox x c) ∨ Inc x h

theorem fourPrivateCells (F : Finset Box) (b : Box) :
    ∃ T ⊆ needsRepair F b, T.card ≤ 4 ∧ ∀ h : H, (∀ x ∈ T, Inc x h) ↔ replaces F b h := by
  classical
  obtain ⟨T,sub,size,all⟩ := compressCells (needsRepair F b)
  refine ⟨T,sub,size,fun h => (all h).trans ⟨?_,?_⟩⟩
  · intro all x zero
    by_cases covered : ∃ c ∈ F.erase b, inBox x c
    · exact Or.inl covered
    · exact Or.inr (all x (mem_filter.mpr ⟨mem_univ _,zero,covered⟩))
  · intro ok x hx
    obtain ⟨zero,unique⟩ := (mem_filter.mp hx).2
    exact (ok x zero).resolve_left unique

theorem privateInside {F : Finset Box} {b : Box}
    (cover : ∀ x : Cell, bit x.1 x.2 = false → ∃ c ∈ F, inBox x c)
    {x : Cell} (own : x ∈ needsRepair F b) : inBox x b := by
  obtain ⟨zero,unique⟩ := (mem_filter.mp own).2
  obtain ⟨c,hc,hit⟩ := cover x zero
  by_cases e : c = b
  · exact e ▸ hit
  · exact False.elim (unique ⟨c,mem_erase.mpr ⟨e,hc⟩,hit⟩)

theorem fourNecessary : Crown Inc 4 := by
  choose h hit using sharpFour.2.1
  refine ⟨sharp,h,fun i j => ⟨?_,fun ne => hit j i ne.symm⟩⟩
  intro yes same
  subst i
  obtain ⟨k,no⟩ := sharpFour.1 (h j)
  by_cases eq : k = j
  · exact no (eq.symm ▸ yes)
  · exact no (hit j k (Ne.symm eq))

#print axioms fourPrivateCells
#print axioms privateInside
#print axioms fourNecessary

end Checkpoint138
