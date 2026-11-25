import EdgeSeparation

namespace Checkpoint125.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def lost (w : Wire 14) := univ.filter (fun i : Fin 21 => edge i∉survivors w)
def ends (i : Fin 21) : Finset V := {endpoint i false,endpoint i true}
def endpoints (L : Finset (Fin 21)) := L.biUnion ends
theorem endsSize : ∀ i, (ends i).card=2 := by decide +kernel
def positive (i : Fin 21) := pair (endpoint i false) (endpoint i true)

/-- Keep the opposite endpoint and the nonneighbors of that endpoint on
the target vertex's side of the bipartition. -/
def negative (i : Fin 21) (k : Bool) (x : V) := decide (x=endpoint i (!k) ∨
  ((x.val<7 ↔ (endpoint i k).val<7) ∧ ¬G.Adj (endpoint i (!k)) x))

instance predicateDec (z : V → Bool) : Decidable (predicate z) := by unfold predicate; infer_instance

private theorem table : ∀ (i : Fin 21) (k : Bool), ¬predicate (negative i k) ∧
    negative i k (endpoint i (!k))=true ∧
    ∀ c y : V, G.Adj c (endpoint i k) → s(c,endpoint i k)≠edge i →
       G.Adj c y → y≠endpoint i k → negative i k y=true := by
  set_option maxRecDepth 8000 in
  set_option maxHeartbeats 0 in
  decide +kernel

theorem positiveYes (i : Fin 21) : predicate (positive i) :=
  (orientation _).mpr ⟨_,_,indexedAdj i,by simp [positive,pair],by simp [positive,pair]⟩
theorem negativeNo (i k) : ¬predicate (negative i k) := (table i k).1

theorem onlyLiteral {H : Finset (Sym2 V)} (sub : H⊆G.edgeFinset) {i : Fin 21}
    (missing : edge i∉H) (k : Bool) {S} (regular : Regular H S)
    (on : lit S (positive i)) (off : ¬lit S (negative i k)) : S={endpoint i k} := by
  obtain ⟨_,other,bound⟩ := table i k
  obtain ⟨x,hx,hit⟩ := on
  have sides : x=endpoint i false ∨ x=endpoint i true := by simpa [positive,pair] using hit
  have atTarget : endpoint i k∈S := by
    have neq : x≠endpoint i (!k) := fun eq => off ⟨x,hx,eq ▸ other⟩
    cases k <;> simp only [Bool.not_true,Bool.not_false] at neq ⊢ <;> rcases sides with rfl|rfl <;> tauto
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨atTarget,?_⟩
  intro y hy
  rcases regular with small|⟨c,adj⟩
  · exact card_le_one.mp small y hy _ atTarget
  · by_contra ne
    have edgeAt := adj _ atTarget
    exact off ⟨y,hy,bound c y (by simpa using sub edgeAt) (fun eq => missing (eq ▸ edgeAt))
      (by simpa using sub (adj _ hy)) ne⟩

theorem lostEdges (w : Wire 14) : (lost w).image edge=G.edgeFinset \ survivors w := by
  ext e
  simp only [lost,mem_image,mem_filter,mem_univ,true_and,mem_sdiff]
  constructor
  · rintro ⟨i,no,rfl⟩
    exact ⟨indexedEdges ▸ mem_image.mpr ⟨i,mem_univ _,rfl⟩,no⟩
  · rintro ⟨he,no⟩
    rw [←indexedEdges] at he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    exact ⟨i,no,rfl⟩

theorem lostSize (w : Wire 14) : (lost w).card=missed w := by
  have inj : Function.Injective edge := by
    change ∀ i j : Fin 21, edge i=edge j → i=j
    decide +kernel
  rw [missed,←lostEdges,card_image_of_injective _ inj]

#print axioms onlyLiteral
end Checkpoint125.Heawood
