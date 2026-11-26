import Dynamics

namespace Checkpoint134.OrderFive
open Finset
open PEqualNP.Outside.L_meta_9338 (V Box legal bit hit)
def rows (x : V) : V := ([0, 11, 5, 12, 2, 3, 13, 19, 6, 15, 1, 9, 4, 17, 8, 10, 7, 14, 16, 20, 18] : List V)[x.val]!
def columns (x : V) : V := ([7, 10, 12, 19, 2, 20, 18, 5, 11, 1, 8, 9, 3, 13, 15, 6, 14, 0, 16, 4, 17] : List V)[x.val]!
def family : List Box := [
  ({0, 7, 16, 18, 19, 20}, {1, 8, 9, 10, 11, 13}),
  ({1, 10, 12, 13, 14, 15}, {2, 3, 4, 5, 7, 16}),
  ({1, 4, 8, 10, 11, 17}, {2, 5, 12, 14, 19, 20}),
  ({1, 2, 6, 9, 11, 14}, {3, 4, 12, 15, 17, 20}),
  ({5, 8, 9, 11, 13, 15}, {0, 2, 3, 6, 17, 19}),
  ({3, 6, 9, 10, 15, 17}, {0, 4, 7, 12, 18, 19}),
  ({3, 4, 10, 12, 16, 20}, {1, 5, 7, 13, 14, 18}),
  ({1, 2, 4, 7, 12, 18}, {5, 10, 13, 15, 16, 20}),
  ({2, 4, 5, 11, 16, 19}, {6, 8, 13, 14, 17, 20}),
  ({2, 3, 5, 7, 9, 20}, {0, 11, 13, 15, 17, 18}),
  ({3, 5, 12, 15, 18, 19}, {0, 6, 7, 9, 13, 16}),
  ({0, 11, 14, 15, 17, 19}, {2, 4, 6, 8, 9, 12}),
  ({0, 8, 9, 10, 14, 20}, {1, 2, 3, 11, 12, 18}),
  ({0, 1, 6, 8, 15, 18}, {3, 9, 10, 12, 16, 19}),
  ({0, 6, 10, 11, 13, 16}, {1, 3, 4, 8, 14, 19}),
  ({0, 1, 7, 9, 13, 17}, {2, 4, 10, 11, 15, 19})]

def permute (b : Box) : Box := (univ.filter (fun x => rows x∈b.1),univ.filter (fun y => columns y∈b.2))

theorem orderFive :
    (∀x : V,rows (rows (rows (rows (rows x))))=x ∧ columns (columns (columns (columns (columns x))))=x) ∧
    rows 1≠1 ∧ ∀x y : V,bit (rows x) (columns y)=bit x y := by decide +kernel

theorem witness : family.toFinset.card=16 ∧ (∀b∈family,legal b) ∧
    covers family.toFinset ∧ ∀b∈family,permute b∈family := by
  have ok : ∀t : Fin family.length,∀x y : V,x∈(family.get t).1 → y∈(family.get t).2 → bit x y=false := by decide +kernel
  have all : ∀x y : V,bit x y=false → ∃t : Fin family.length,hit (family.get t) x y := by
    unfold hit; decide +kernel
  have perm : ∀t : Fin family.length,∃u : Fin family.length,permute (family.get t)=family.get u := by decide +kernel
  refine ⟨by decide +kernel,?_,?_,?_⟩
  · intro b hb x hx y hy
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    exact ok t x y hx hy
  · intro x y z
    obtain ⟨t,ht⟩ := all x y z
    exact ⟨family.get t,List.mem_toFinset.mpr (family.get_mem _),ht⟩
  · intro b hb
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    obtain ⟨u,hu⟩ := perm t
    exact hu ▸ family.get_mem u
#print axioms orderFive
#print axioms witness
end Checkpoint134.OrderFive
