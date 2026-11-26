import FamilyBound
import PlaneMinimum
import Mathlib.Tactic.Abel

namespace Checkpoint134
open Finset
open PEqualNP.Outside.L_meta_9338 (V Box bit legal)
def translate (k : V) (b : Box) : Box :=
  (univ.filter (fun x : V => x+k ∈ b.1),univ.filter (fun y : V => y+k ∈ b.2))
def translated (k : V) (s : Finset Box) := s.image (translate k)
theorem translateZero (b : Box) : translate 0 b=b := by apply Prod.ext <;> ext x <;> simp [translate]
theorem translateAdd (p q : V) (b : Box) : translate p (translate q b)=translate (p+q) b := by
  apply Prod.ext <;> ext x <;> simp [translate,add_assoc]
theorem translatedZero (s : Finset Box) : translated 0 s=s := by
  have e : translate 0=id := funext translateZero
  simp [translated,e]
theorem translatedAdd (p q : V) (s : Finset Box) : translated p (translated q s)=translated (p+q) s := by
  simp [translated,image_image,Function.comp_def,translateAdd]
theorem orbitOfLower
    (bound : ∀{s : Finset Box},(∀b∈s,legal b) → covers s → stable s → 15≤s.card)
    {s : Finset Box} (g : ∀b∈s,legal b) (complete : covers s) (small : s.card<15) :
    (univ.image (fun k : V => translated k s)).card=21 := by
  have inject : Function.Injective (fun k : V => translated k s) := by
    intro p q e
    by_contra ne
    let k := p-q
    have nz : k≠0 := sub_ne_zero.mpr ne
    have fixed : translated k s=s := by
      have h := congrArg (translated (-q)) e
      simpa only [translatedAdd,k,neg_add_cancel,translatedZero,neg_add_eq_sub] using h
    have iter (n : ℕ) : translated (n • k) s=s := by
      induction n with
      | zero => simp [translatedZero]
      | succ n ih => rw [succ_nsmul,←translatedAdd,fixed,ih]
    have cyclic : ∀v : V,v≠0 → ∃t : Fin 21,t.val • v=7 ∨ t.val • v=3 := by decide +kernel
    obtain ⟨n,eq|eq⟩ := cyclic k nz
    · have h : translated 7 s=s := eq ▸ iter n.val
      have closed : stable s := by
        intro b hb
        have hm : translate 7 b∈translated 7 s := mem_image_of_mem _ hb
        exact h ▸ hm
      exact (Nat.not_le_of_gt small) (bound g complete closed)
    · have h : translated 3 s=s := eq ▸ iter n.val
      have coordinate : ∀v : V,Checkpoint133.Plane.move 1 v=v+3 := by decide +kernel
      have compatible (b : Box) : Checkpoint133.Plane.turn 1 b=translate 3 b := by
        apply Prod.ext <;> ext x <;> simp [translate,Checkpoint133.Plane.turn,coordinate]
      have closed : ∀ b∈s,Checkpoint133.Plane.turn 1 b∈s := by
        intro b hb
        rw [compatible,←h]
        exact mem_image_of_mem _ hb
      have board : ∀ x y : V,Checkpoint133.Plane.zeroCell x y ↔ bit x y=false := by decide +kernel
      have good : ∀ b∈s,Checkpoint133.Plane.Good b := by
        intro b hb x hx y hy
        exact (board x y).mpr (g b hb x hx y hy)
      have cov : Checkpoint133.Plane.FamilyCovers s := fun x y z => complete x y ((board x y).mp z)
      have tooLarge := Checkpoint133.Plane.stableMinimum good cov (Checkpoint133.Plane.stableFromSingleRotation closed)
      omega
  simp [card_image_of_injective _ inject]
def addSeven (b : Box) : Box := (b.1.image (fun x => x+7),b.2.image (fun y => y+7))

theorem forwardPair (b : Box) : addSeven b=spin (spin b) := by
  have cycle : ∀x : V,x+7+7+7=x := by decide +kernel
  have axis (s : Finset V) (p : V) : p∈s.image (fun x => x+7) ↔ p+7+7∈s := by
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      simpa only [cycle] using hx
    · intro h
      exact mem_image.mpr ⟨p+7+7,h,cycle p⟩
  apply Prod.ext <;> ext x <;> simp only [addSeven,axis,spinRow,spinCol]

theorem stableForward (s : Finset Box) : stable s ↔ ∀b∈s,addSeven b∈s := by
  constructor
  · intro closed b hb
    rw [forwardPair]
    exact closed _ (closed _ hb)
  · intro closed b hb
    have h := closed _ (closed b hb)
    simpa only [forwardPair,period] using h

def translationOrbit (s : Finset Box) := univ.image (fun k : V => translated k s)

theorem sameOrbit (p : V) (t s : Finset Box) : translated p t∈translationOrbit s ↔ t∈translationOrbit s := by
  constructor
  · intro h
    obtain ⟨k,_,e⟩ := mem_image.mp h
    have inverse := congrArg (translated (-p)) e
    exact mem_image.mpr ⟨-p+k,mem_univ _,by simpa only [translatedAdd,neg_add_cancel,translatedZero] using inverse⟩
  · intro h
    obtain ⟨k,_,rfl⟩ := mem_image.mp h
    exact mem_image.mpr ⟨p+k,mem_univ _,(translatedAdd p k s).symm⟩

theorem countByOrbits (u : Finset (Finset Box)) (free : ∀s∈u,(translationOrbit s).card=21)
    (closed : ∀s∈u,∀k : V,translated k s∈u) : 21 ∣ u.card := by
  induction u using Finset.strongInductionOn
  rename_i u ih
  by_cases empty : u=∅
  · simp [empty]
  obtain ⟨s,hs⟩ := nonempty_iff_ne_empty.mpr empty
  have inside : translationOrbit s ⊆ u := by
    intro t ht
    obtain ⟨k,_,rfl⟩ := mem_image.mp ht
    exact closed s hs k
  let v := u \ translationOrbit s
  have sv : s∈translationOrbit s := mem_image.mpr ⟨0,mem_univ _,translatedZero _⟩
  have lt : v ⊂ u := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,?_⟩
    intro e
    have h : s∈v := e ▸ hs
    exact (mem_sdiff.mp h).2 sv
  have disjointRest : ∀t∈v,∀k : V,translated k t∈v := by
    intro t ht k
    obtain ⟨ht,out⟩ := mem_sdiff.mp ht
    exact mem_sdiff.mpr ⟨closed t ht k,fun h => out ((sameOrbit ..).mp h)⟩
  have divides := ih v lt (fun t ht => free t (mem_sdiff.mp ht).1) disjointRest
  have count := card_sdiff_add_card_eq_card inside
  rw [←count,free s hs]
  exact dvd_add divides (dvd_refl 21)

end Checkpoint134
