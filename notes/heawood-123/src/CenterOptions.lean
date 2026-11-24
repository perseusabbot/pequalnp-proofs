import FourProfiles

namespace Checkpoint123.Heawood
open Finset SimpleGraph
open Checkpoint122.Pruning
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Four-edge omissions compatible with a fixed six-center cover of seventeen surviving edges. -/
def centerOptions (C : Finset V) : Finset (Finset (Sym2 V)) :=
  let I := incident C
  if I.card=17 then {G.edgeFinset \ I}
  else if I.card=18 then I.image (fun e => insert e (G.edgeFinset \ I))
  else ∅

/-- Membership in the finite census is witnessed by a six-vertex center set. -/
def SixCenterOption (L : Finset (Sym2 V)) : Prop :=
  ∃ C : Finset V, C.card=6 ∧ L∈centerOptions C

theorem optionsOfSix {w : Wire 14} (sound : ∀ z, accepts w z → predicate z)
    (six : w.jobs.card=6) (loss : missed w=4) : SixCenterOption (G.edgeFinset \ survivors w) := by
  obtain ⟨C,sz,sub,edges,counts⟩ := sixCenterCover sound six loss
  refine ⟨C,sz,?_⟩
  rcases counts with h|h
  · have eq := eq_of_subset_of_card_le sub (by omega)
    simp [centerOptions,h,eq]
  · have one : (incident C \ survivors w).card=1 := by rw [card_sdiff_of_subset sub,h,edges]
    obtain ⟨e,unique⟩ := card_eq_one.mp one
    have isE : e ∈ incident C \ survivors w := unique ▸ mem_singleton_self e
    have hE := mem_sdiff.mp isE
    have source : incident C ⊆ G.edgeFinset := by
      intro x hx
      obtain ⟨v,_,mem⟩ := mem_biUnion.mp hx
      obtain ⟨u,hu,rfl⟩ := mem_image.mp mem
      have adj : G.Adj v u := List.mem_toFinset.mp hu
      simpa using adj
    simp only [centerOptions,h,show (18:ℕ)≠17 by decide,ite_false,ite_true]
    apply mem_image.mpr
    refine ⟨e,hE.1,?_⟩
    ext x
    constructor
    · intro hx
      rcases mem_insert.mp hx with rfl|miss
      · exact mem_sdiff.mpr ⟨source hE.1,hE.2⟩
      · have p := mem_sdiff.mp miss
        exact mem_sdiff.mpr ⟨p.1,fun old => p.2 (sub old)⟩
    · intro hx
      have p := mem_sdiff.mp hx
      by_cases hxI : x∈incident C
      · have seen : x∈incident C \ survivors w := mem_sdiff.mpr ⟨hxI,p.2⟩
        rw [unique] at seen
        exact mem_insert.mpr (Or.inl (mem_singleton.mp seen))
      · exact mem_insert_of_mem (mem_sdiff.mpr ⟨p.1,hxI⟩)

#print axioms optionsOfSix
end Checkpoint123.Heawood
