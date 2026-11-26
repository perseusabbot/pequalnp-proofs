import Dynamics
import Actions
import PEqualNP.Outside.L_meta_9351

namespace Checkpoint134
open Finset
open PEqualNP.Outside.L_meta_9338 (V Box legal hit bit)
abbrev Slots (m f : ℕ) (a : Fin m → Box) (d : Fin f → FixedPool.Index) :=
  ∀ x y : V,bit x y=false → (∃t,FixedPool.contains (d t) x y) ∨ ∃t,Hit (a t) x y
abbrev PairSlots (k : Actions.Class) (a : Fin 4 → Box) :=
  ∀ x y : V,bit x y=false → (FixedPool.contains 0 x y ∨ FixedPool.contains (Actions.rep k) x y) ∨ ∃ t,Hit (a t) x y

theorem pad {α} (l : List α) (default : α) (n : ℕ) (le : l.length≤n) :
    ∃ v : Fin n→α,(∀a∈l,∃t,v t=a) ∧ (∀t,v t∈l ∨ v t=default) := by
  let v (t : Fin n) := if h : t.val<l.length then l.get ⟨t.val,h⟩ else default
  refine ⟨v,?_,?_⟩
  · intro a ha
    obtain ⟨k,rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨⟨k.val,k.isLt.trans_le le⟩,by simp [v,k.isLt]⟩
  · intro t
    by_cases h : t.val<l.length
    · exact Or.inl (by simpa [v,h] using l.get_mem ⟨t.val,h⟩)
    · exact Or.inr (by simp [v,h])

theorem coveredSlots {s : Finset Box} (good : ∀b∈s,legal b) (complete : covers s)
    {fs ms : List Box} (fix : ∀b∈fs,b∈s ∧ spin b=b) (mov : ∀b∈ms,b∈s)
    (parts : ∀b∈s,b∈fs ∨ ∃c∈ms,b∈orbit c) (m f : ℕ) (lm : ms.length≤m) (lf : fs.length≤f) :
    ∃ (a : Fin m→Box) (d : Fin f→FixedPool.Index),(∀t,legal (a t)) ∧ Slots m f a d := by
  let blank : Box := (∅,∅)
  have eg : legal blank := by simp [blank,legal]
  have eb : spin blank=blank := by apply Prod.ext <;> ext x <;> simp [blank,spin]
  obtain ⟨a,mapA,typeA⟩ := pad ms blank m lm
  obtain ⟨b,mapB,typeB⟩ := pad fs blank f lf
  have one (t : Fin f) : ∃k : FixedPool.Index,∀x y,hit (b t) x y → FixedPool.contains k x y := by
    apply fixedContains
    · rcases typeB t with h|h
      · exact good _ (fix _ h).1
      · simpa only [h] using eg
    · rcases typeB t with h|h
      · exact (fix _ h).2
      · simpa only [h] using eb
  choose d hd using one
  refine ⟨a,d,?_,?_⟩
  · intro t
    rcases typeA t with h|h
    · exact good _ (mov _ h)
    · simpa only [h] using eg
  · intro x y z
    obtain ⟨w,hw,wh⟩ := complete x y z
    rcases parts w hw with h|⟨c,hc,orb⟩
    · obtain ⟨t,ht⟩ := mapB w h
      exact Or.inl ⟨t,hd _ x y (ht ▸ wh)⟩
    · obtain ⟨t,ht⟩ := mapA c hc
      exact Or.inr ⟨t,ht ▸ orbitHit c w orb wh⟩

theorem reducePair (a : Fin 4→Box) (d : Fin 2→FixedPool.Index)
    (g : ∀t,legal (a t)) (cov : Slots 4 2 a d) :
    ∃ (k : Actions.Class) (b : Fin 4→Box),(∀t,legal (b t)) ∧ PairSlots k b := by
  obtain ⟨h,k,relation⟩ := Actions.classify (d 0) (d 1)
  refine ⟨k,fun t => Actions.pull h (a t),fun t => Actions.pullLegal _ _ (g t),?_⟩
  intro x y z
  rcases cov (Actions.point h x y).1 (Actions.point h x y).2 ((Actions.preserves ..).trans z) with ⟨t,ht⟩|⟨t,ht⟩
  · apply Or.inl
    apply relation
    fin_cases t
    · exact Or.inl ht
    · exact Or.inr ht
  · exact Or.inr ⟨t,Actions.pullOrbit _ _ _ _ ht⟩

theorem familyLower
    (two : ∀ a d,(∀t,legal (a t)) → Slots 2 14 a d → False)
    (three : ∀ a d,(∀t,legal (a t)) → Slots 3 5 a d → False)
    (four : ∀ k a,(∀t,legal (a t)) → PairSlots k a → False)
    {s : Finset Box} (good : ∀b∈s,legal b) (complete : covers s) (closed : stable s) :
    15≤s.card := by
  by_contra! small
  obtain ⟨fs,ms,n,fix,mov,parts⟩ := decompose s closed
  by_cases few : ms.length≤2
  · obtain ⟨a,d,g,c⟩ := coveredSlots good complete fix mov parts 2 14 few (by omega)
    exact two a d g c
  · by_cases med : ms.length≤3
    · obtain ⟨a,d,g,c⟩ := coveredSlots good complete fix mov parts 3 5 med (by omega)
      exact three a d g c
    · obtain ⟨a,d,g,c⟩ := coveredSlots good complete fix mov parts 4 2 (by omega) (by omega)
      obtain ⟨k,b,gb,cb⟩ := reducePair a d g c
      exact four k b gb cb

/-- The upstream family attaining fifteen is also closed under the order-three rotation. -/
theorem incumbent : ∃ L : List Box, L.length=15 ∧
    (∀b∈L,legal b) ∧ covers L.toFinset ∧ stable L.toFinset := by
  let L := PEqualNP.Outside.L_meta_9351.cover
  have ok : ∀t : Fin L.length, ∀x y : V,x∈(L.get t).1 → y∈(L.get t).2 → bit x y=false := by decide +kernel
  have all : ∀x y : V,bit x y=false → ∃t : Fin L.length,hit (L.get t) x y := by
    unfold hit; decide +kernel
  have rotate : ∀t : Fin L.length,∃u : Fin L.length,spin (L.get t)=L.get u := by decide +kernel
  refine ⟨L,by decide,?_,?_,?_⟩
  · intro b hb x hx y hy
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hb
    exact ok t x y hx hy
  · intro x y z
    obtain ⟨t,ht⟩ := all x y z
    exact ⟨L.get t,List.mem_toFinset.mpr (L.get_mem _),ht⟩
  · intro b hb
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hb)
    obtain ⟨u,hu⟩ := rotate t
    exact hu ▸ List.mem_toFinset.mpr (L.get_mem u)
#print axioms incumbent
end Checkpoint134
