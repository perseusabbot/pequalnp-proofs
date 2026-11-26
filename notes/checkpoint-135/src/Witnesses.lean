import OrbitGeometry

namespace Checkpoint135.Witnesses
open Finset
open PEqualNP.Outside.L_meta_9338 (V Box bit hit legal)

def covers (L : List Box) : Prop := ∀ x y : V, bit x y=false → ∃ b∈L, hit b x y

def pull (R : Rotation) (b : Box) : Box :=
  (univ.filter (fun x => R.row x ∈ b.1), univ.filter (fun y => R.col y ∈ b.2))

namespace Triangle
def row : Array V := #[0, 4, 10, 15, 14, 2, 8, 18, 12, 11, 5, 17, 6, 3, 1, 13, 16, 9, 19, 7, 20]
def col : Array V := #[0, 9, 15, 14, 19, 7, 4, 17, 11, 10, 1, 13, 2, 8, 18, 12, 16, 5, 3, 6, 20]
def rotation : Rotation := ⟨fun x => row.getD x.val 0, fun y => col.getD y.val 0⟩
def family : List Box := [
  ({4, 6, 7, 8, 9, 16}, {1, 10, 17, 18, 19, 20}),
  ({1, 4, 7, 8, 10, 11, 13, 15, 17}, {2, 5, 19}),
  ({0, 1, 3, 5, 7, 18}, {9, 11, 13, 15, 16, 19}),
  ({8, 11, 12, 14, 16, 18}, {1, 3, 5, 6, 9, 20}),
  ({3, 4, 5, 9, 12, 13, 14, 17, 18}, {6, 7, 15}),
  ({0, 7, 10, 13, 14, 19}, {1, 2, 4, 8, 11, 16}),
  ({1, 2, 3, 6, 9, 11, 14, 15, 19}, {4, 12, 17}),
  ({1, 6, 12, 16, 17, 19}, {4, 7, 9, 10, 14, 20}),
  ({2, 5, 6, 7, 8, 10, 12, 18, 19}, {0, 16, 20}),
  ({0, 2, 4, 15, 18, 19}, {6, 8, 10, 12, 13, 16}),
  ({2, 5, 6, 11, 13, 20}, {0, 3, 8, 14, 15, 17}),
  ({5, 9, 10, 12, 15, 20}, {0, 2, 3, 7, 13, 18}),
  ({2, 3, 8, 10, 17, 20}, {0, 5, 11, 12, 14, 18}),
  ({0, 5, 6, 7, 14, 15, 16, 17, 20}, {8, 9, 18}),
  ({0, 1, 2, 8, 9, 13, 16, 18, 20}, {3, 10, 11}),
  ({0, 3, 4, 10, 11, 12, 16, 19, 20}, {1, 13, 14})]
theorem action : (∀ x,rotation.row (rotation.row (rotation.row x))=x ∧
    rotation.col (rotation.col (rotation.col x))=x) ∧ (∃x,rotation.row x≠x) ∧
    ∀ x y,bit (rotation.row x) (rotation.col y)=bit x y := by decide +kernel

theorem upper : family.toFinset.card=16 ∧ (∀b∈family,legal b) ∧ covers family ∧
    ∀b∈family,pull rotation b∈family := by
  have ok : ∀t : Fin family.length,∀x y : V,x∈(family.get t).1 → y∈(family.get t).2 →
      bit x y=false := by decide +kernel
  have all : ∀x y : V,bit x y=false → ∃t : Fin family.length,hit (family.get t) x y := by
    unfold hit; decide +kernel
  have stable : ∀t : Fin family.length,∃j : Fin family.length,pull rotation (family.get t)=family.get j := by
    decide +kernel
  refine ⟨by decide +kernel,?_,?_,?_⟩
  · intro b hb x hx y hy
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    exact ok t x y hx hy
  · intro x y z
    obtain ⟨t,h⟩ := all x y z
    exact ⟨family.get t,family.get_mem _,h⟩
  · intro b hb
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    obtain ⟨j,h⟩ := stable t
    exact h ▸ family.get_mem j
#print axioms action
#print axioms upper
end Triangle

namespace Homology
def row : Array V := #[0, 6, 11, 3, 19, 12, 10, 7, 2, 18, 1, 8, 16, 13, 9, 15, 5, 4, 14, 17, 20]
def col : Array V := #[5, 11, 10, 3, 19, 17, 6, 7, 2, 18, 8, 15, 12, 9, 14, 1, 4, 0, 13, 16, 20]
def rotation : Rotation := ⟨fun x => row.getD x.val 0, fun y => col.getD y.val 0⟩
def family : List Box := [
  ({3, 4, 5, 14}, {6, 7, 15, 16, 17, 18}),
  ({0, 1, 6, 10, 15}, {3, 4, 12, 16, 19}),
  ({13, 15}, {0, 2, 3, 4, 5, 6, 7, 8, 10, 16, 17, 19}),
  ({0, 5, 12, 15, 16}, {3, 6, 9, 13, 18}),
  ({5, 7, 8, 9, 10, 17}, {0, 2, 11, 18, 19, 20}),
  ({0, 4, 5, 11, 13, 17}, {2, 6, 8, 14, 15, 19}),
  ({1, 2, 4, 7, 12, 18}, {5, 10, 13, 15, 16, 20}),
  ({3, 16, 17, 18}, {5, 6, 7, 9, 11, 19}),
  ({3, 9, 12, 19}, {0, 1, 4, 6, 7, 13}),
  ({0, 4, 8, 12, 13, 19}, {1, 2, 6, 10, 14, 16}),
  ({6, 7, 11, 14, 16, 19}, {1, 4, 8, 9, 17, 20}),
  ({0, 2, 13, 16, 17, 19}, {4, 6, 8, 10, 11, 14}),
  ({2, 6, 9, 20}, {0, 3, 10, 12, 15, 17, 18}),
  ({1, 8, 14, 20}, {2, 3, 5, 9, 11, 12, 17}),
  ({10, 11, 18, 20}, {0, 1, 3, 5, 8, 12, 13}),
  ({1, 3, 4, 6, 10, 17, 19, 20}, {7, 12, 14})]
theorem action : (∀ x,rotation.row (rotation.row (rotation.row x))=x ∧
    rotation.col (rotation.col (rotation.col x))=x) ∧ (∃x,rotation.row x≠x) ∧
    ∀ x y,bit (rotation.row x) (rotation.col y)=bit x y := by decide +kernel

theorem upper : family.toFinset.card=16 ∧ (∀b∈family,legal b) ∧ covers family ∧
    ∀b∈family,pull rotation b∈family := by
  have ok : ∀t : Fin family.length,∀x y : V,x∈(family.get t).1 → y∈(family.get t).2 →
      bit x y=false := by decide +kernel
  have all : ∀x y : V,bit x y=false → ∃t : Fin family.length,hit (family.get t) x y := by
    unfold hit; decide +kernel
  have stable : ∀t : Fin family.length,∃j : Fin family.length,pull rotation (family.get t)=family.get j := by
    decide +kernel
  refine ⟨by decide +kernel,?_,?_,?_⟩
  · intro b hb x hx y hy
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    exact ok t x y hx hy
  · intro x y z
    obtain ⟨t,h⟩ := all x y z
    exact ⟨family.get t,family.get_mem _,h⟩
  · intro b hb
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    obtain ⟨j,h⟩ := stable t
    exact h ▸ family.get_mem j
#print axioms action
#print axioms upper
end Homology

namespace Polarity
def colPartner : Array V := #[3, 9, 1, 5, 0, 2, 10, 17, 16, 8, 6, 13, 14, 18, 11, 19, 4, 7, 12, 20, 15]
def rowPartner : Array V := #[4, 2, 5, 0, 16, 3, 10, 17, 9, 1, 6, 14, 18, 11, 12, 20, 8, 7, 13, 15, 19]
def rowToCol (x : V) := colPartner.getD x.val 0
def colToRow (y : V) := rowPartner.getD y.val 0
def dual (b : Box) : Box := (univ.filter (fun x => rowToCol x∈b.2),univ.filter (fun y => colToRow y∈b.1))
def seed : List Box := [
  ({0, 1, 6, 8, 15, 18}, {3, 9, 10, 12, 16, 19}),
  ({1, 3, 7, 11, 15, 16}, {4, 5, 9, 13, 17, 19}),
  ({0, 4, 5, 11, 13, 17}, {2, 6, 8, 14, 15, 19}),
  ({0, 2, 4, 7, 9, 12, 20}, {10, 13, 15, 18}),
  ({3, 4, 12, 13, 14, 18}, {1, 5, 6, 7, 15, 16}),
  ({0, 3, 7, 9, 10, 13, 16}, {1, 4, 11, 19}),
  ({6, 11, 13, 20}, {0, 1, 3, 8, 14, 15, 17}),
  ({4, 8, 9, 11, 14, 19}, {1, 2, 6, 12, 17, 20}),
  ({2, 5, 7, 10, 18, 19}, {0, 8, 11, 13, 16, 20}),
  ({2, 14, 15, 16}, {3, 4, 5, 6, 8, 17, 18}),
  ({1, 5, 7, 14, 20}, {2, 9, 11, 15, 17}),
  ({5, 9, 10, 12, 15, 20}, {0, 2, 3, 7, 13, 18}),
  ({1, 6, 12, 16, 17, 19}, {4, 7, 9, 10, 14, 20}),
  ({2, 3, 8, 10, 17, 20}, {0, 5, 11, 12, 14, 18})]
theorem board : (∀x,colToRow (rowToCol x)=x ∧ rowToCol (colToRow x)=x) ∧
    (∀x y,bit (colToRow y) (rowToCol x)=bit x y) ∧ (colToRow 18,rowToCol 6)=(13,10) := by decide +kernel

theorem holes : ∀ x y : V, bit x y=false →
    ((¬ ∃t : Fin seed.length,hit (seed.get t) x y) ↔ (x=6 ∧ y=18) ∨ (x=13 ∧ y=10)) := by
  unfold hit; decide +kernel

theorem fixedFamily : seed.toFinset.card=14 ∧ (∀b∈seed,legal b) ∧ (∀b∈seed,dual b∈seed) ∧
    (seed.toFinset.filter (fun b => dual b=b)).card=4 := by
  have ok : ∀t : Fin seed.length, ∀ x y : V,x∈(seed.get t).1 → y∈(seed.get t).2 → bit x y=false := by
    decide +kernel
  have perm : ∀t : Fin seed.length,∃j : Fin seed.length,dual (seed.get t)=seed.get j := by decide +kernel
  refine ⟨by decide +kernel,?_,?_,by decide +kernel⟩
  · intro b hb x hx y hy
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    exact ok t x y hx hy
  · intro b hb
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    obtain ⟨j,h⟩ := perm t
    exact h ▸ seed.get_mem j
#print axioms board
#print axioms holes
#print axioms fixedFamily
end Polarity
end Checkpoint135.Witnesses
