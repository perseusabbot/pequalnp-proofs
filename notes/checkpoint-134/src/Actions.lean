import FixedPool

namespace Checkpoint134.Actions
open Finset
open PEqualNP.Outside.L_meta_9338 (V Box bit hit legal)
set_option maxHeartbeats 0
set_option maxRecDepth 16000
def scales : Array ℕ := #[
  1,20,1,20,1,20,1,20,1,20,1,20,1,20,2,19,
  2,19,2,19,2,19,2,19,2,19,2,19,4,17,4,17,
  4,17,4,17,4,17,4,17,4,17,8,13,8,13,8,13,
  8,13,8,13,8,13,8,13,11,10,11,10,11,10,11,10,
  11,10,11,10,11,10,16,5,16,5,16,5,16,5,16,5,
  16,5,16,5
]
def rowOffsets : Array ℕ := #[
  0,0,1,1,2,2,3,3,4,4,5,5,6,6,0,0,
  1,1,2,2,3,3,4,4,5,5,6,6,0,0,1,1,
  2,2,3,3,4,4,5,5,6,6,0,0,1,1,2,2,
  3,3,4,4,5,5,6,6,0,0,1,1,2,2,3,3,
  4,4,5,5,6,6,0,0,1,1,2,2,3,3,4,4,
  5,5,6,6
]
def colOffsets : Array ℕ := #[
  0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,
  8,8,9,9,10,10,11,11,12,12,13,13,0,0,1,1,
  2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,
  10,10,11,11,12,12,13,13,7,7,8,8,9,9,10,10,
  11,11,12,12,13,13,0,0,1,1,2,2,3,3,4,4,
  5,5,6,6
]
def duals : Array ℕ := #[
  0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,
  0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,
  0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,
  0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,
  0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,
  0,1,0,1
]
def selections : Array ℕ := #[
  0,0,56,136,1,112,2,96,113,114,48,58,57,3,0,0,
  8,64,66,144,9,120,65,10,104,121,11,118,56,8,6,16,
  129,72,74,152,19,17,128,73,126,6,136,64,16,5,81,24,
  137,80,134,82,160,27,14,5,1,66,129,81,1,35,44,150,
  92,108,38,36,124,148,112,144,72,24,35,13,89,32,22,145,
  88,142,13,62,2,9,74,137,44,89,2,43,132,52,158,100,
  156,60,96,120,152,80,150,32,43,21,21,97,40,30,70,117,
  113,65,19,134,92,22,132,21,19,164,78,28,20,76,114,10,
  17,82,108,145,52,97,164,4,51,140,68,4,48,104,128,160,
  38,88,158,40,78,51,29,29,125,61,58,121,73,27,36,142,
  100,30,28,140,29,27,84,116,57,11,126,14,124,13,156,70,
  20,68,125,84,11,12,3,118,6,5,148,62,60,117,76,4,
  61,116,12,3
]
def img0 : Array ℕ := #[
  0,1,2,3,4,5,6,7,8,9,10,11,12,13
]
def img1 : Array ℕ := #[
  13,9,6,4,3,11,2,8,7,1,12,5,10,0
]
def img2 : Array ℕ := #[
  1,2,3,5,6,7,9,10,11,13,0,4,8,12
]
def img3 : Array ℕ := #[
  12,13,9,6,5,4,3,11,10,2,8,7,0,1
]
def img4 : Array ℕ := #[
  2,3,5,7,9,10,13,0,4,12,1,6,11,8
]
def img5 : Array ℕ := #[
  8,12,13,9,7,6,5,4,0,3,11,10,1,2
]
def img6 : Array ℕ := #[
  3,5,7,10,13,0,12,1,6,8,2,9,4,11
]
def img7 : Array ℕ := #[
  11,8,12,13,10,9,7,6,1,5,4,0,2,3
]
def img8 : Array ℕ := #[
  5,7,10,0,12,1,8,2,9,11,3,13,6,4
]
def img9 : Array ℕ := #[
  4,11,8,12,0,13,10,9,2,7,6,1,3,5
]
def img10 : Array ℕ := #[
  7,10,0,1,8,2,11,3,13,4,5,12,9,6
]
def img11 : Array ℕ := #[
  6,4,11,8,1,12,0,13,3,10,9,2,5,7
]
def img12 : Array ℕ := #[
  10,0,1,2,11,3,4,5,12,6,7,8,13,9
]
def img13 : Array ℕ := #[
  9,6,4,11,2,8,1,12,5,0,13,3,7,10
]
def img14 : Array ℕ := #[
  0,2,5,10,12,1,11,3,4,6,7,9,8,13
]
def img15 : Array ℕ := #[
  13,6,11,12,10,9,5,4,3,2,8,1,7,0
]
def img16 : Array ℕ := #[
  1,3,7,0,8,2,4,5,6,9,10,13,11,12
]
def img17 : Array ℕ := #[
  12,9,4,8,0,13,7,6,5,3,11,2,10,1
]
def img18 : Array ℕ := #[
  2,5,10,1,11,3,6,7,9,13,0,12,4,8
]
def img19 : Array ℕ := #[
  8,13,6,11,1,12,10,9,7,5,4,3,0,2
]
def img20 : Array ℕ := #[
  3,7,0,2,4,5,9,10,13,12,1,8,6,11
]
def img21 : Array ℕ := #[
  11,12,9,4,2,8,0,13,10,7,6,5,1,3
]
def img22 : Array ℕ := #[
  5,10,1,3,6,7,13,0,12,8,2,11,9,4
]
def img23 : Array ℕ := #[
  4,8,13,6,3,11,1,12,0,10,9,7,2,5
]
def img24 : Array ℕ := #[
  7,0,2,5,9,10,12,1,8,11,3,4,13,6
]
def img25 : Array ℕ := #[
  6,11,12,9,5,4,2,8,1,0,13,10,3,7
]
def img26 : Array ℕ := #[
  10,1,3,7,13,0,8,2,11,4,5,6,12,9
]
def img27 : Array ℕ := #[
  9,4,8,13,7,6,3,11,2,1,12,0,5,10
]
def img28 : Array ℕ := #[
  0,5,1,7,8,2,9,10,12,11,3,6,4,13
]
def img29 : Array ℕ := #[
  13,11,9,8,7,6,1,12,10,5,4,2,3,0
]
def img30 : Array ℕ := #[
  1,7,2,10,11,3,13,0,8,4,5,9,6,12
]
def img31 : Array ℕ := #[
  12,4,13,11,10,9,2,8,0,7,6,3,5,1
]
def img32 : Array ℕ := #[
  2,10,3,0,4,5,12,1,11,6,7,13,9,8
]
def img33 : Array ℕ := #[
  8,6,12,4,0,13,3,11,1,10,9,5,7,2
]
def img34 : Array ℕ := #[
  3,0,5,1,6,7,8,2,4,9,10,12,13,11
]
def img35 : Array ℕ := #[
  11,9,8,6,1,12,5,4,2,0,13,7,10,3
]
def img36 : Array ℕ := #[
  5,1,7,2,9,10,11,3,6,13,0,8,12,4
]
def img37 : Array ℕ := #[
  4,13,11,9,2,8,7,6,3,1,12,10,0,5
]
def img38 : Array ℕ := #[
  7,2,10,3,13,0,4,5,9,12,1,11,8,6
]
def img39 : Array ℕ := #[
  6,12,4,13,3,11,10,9,5,2,8,0,1,7
]
def img40 : Array ℕ := #[
  10,3,0,5,12,1,6,7,13,8,2,4,11,9
]
def img41 : Array ℕ := #[
  9,8,6,12,5,4,0,13,7,3,11,1,2,10
]
def img42 : Array ℕ := #[
  0,1,2,3,4,5,6,7,8,9,10,11,12,13
]
def img43 : Array ℕ := #[
  13,9,6,4,3,11,2,8,7,1,12,5,10,0
]
def img44 : Array ℕ := #[
  1,2,3,5,6,7,9,10,11,13,0,4,8,12
]
def img45 : Array ℕ := #[
  12,13,9,6,5,4,3,11,10,2,8,7,0,1
]
def img46 : Array ℕ := #[
  2,3,5,7,9,10,13,0,4,12,1,6,11,8
]
def img47 : Array ℕ := #[
  8,12,13,9,7,6,5,4,0,3,11,10,1,2
]
def img48 : Array ℕ := #[
  3,5,7,10,13,0,12,1,6,8,2,9,4,11
]
def img49 : Array ℕ := #[
  11,8,12,13,10,9,7,6,1,5,4,0,2,3
]
def img50 : Array ℕ := #[
  5,7,10,0,12,1,8,2,9,11,3,13,6,4
]
def img51 : Array ℕ := #[
  4,11,8,12,0,13,10,9,2,7,6,1,3,5
]
def img52 : Array ℕ := #[
  7,10,0,1,8,2,11,3,13,4,5,12,9,6
]
def img53 : Array ℕ := #[
  6,4,11,8,1,12,0,13,3,10,9,2,5,7
]
def img54 : Array ℕ := #[
  10,0,1,2,11,3,4,5,12,6,7,8,13,9
]
def img55 : Array ℕ := #[
  9,6,4,11,2,8,1,12,5,0,13,3,7,10
]
def img56 : Array ℕ := #[
  0,5,1,7,8,2,9,10,12,11,3,6,4,13
]
def img57 : Array ℕ := #[
  13,11,9,8,7,6,1,12,10,5,4,2,3,0
]
def img58 : Array ℕ := #[
  1,7,2,10,11,3,13,0,8,4,5,9,6,12
]
def img59 : Array ℕ := #[
  12,4,13,11,10,9,2,8,0,7,6,3,5,1
]
def img60 : Array ℕ := #[
  2,10,3,0,4,5,12,1,11,6,7,13,9,8
]
def img61 : Array ℕ := #[
  8,6,12,4,0,13,3,11,1,10,9,5,7,2
]
def img62 : Array ℕ := #[
  3,0,5,1,6,7,8,2,4,9,10,12,13,11
]
def img63 : Array ℕ := #[
  11,9,8,6,1,12,5,4,2,0,13,7,10,3
]
def img64 : Array ℕ := #[
  5,1,7,2,9,10,11,3,6,13,0,8,12,4
]
def img65 : Array ℕ := #[
  4,13,11,9,2,8,7,6,3,1,12,10,0,5
]
def img66 : Array ℕ := #[
  7,2,10,3,13,0,4,5,9,12,1,11,8,6
]
def img67 : Array ℕ := #[
  6,12,4,13,3,11,10,9,5,2,8,0,1,7
]
def img68 : Array ℕ := #[
  10,3,0,5,12,1,6,7,13,8,2,4,11,9
]
def img69 : Array ℕ := #[
  9,8,6,12,5,4,0,13,7,3,11,1,2,10
]
def img70 : Array ℕ := #[
  0,2,5,10,12,1,11,3,4,6,7,9,8,13
]
def img71 : Array ℕ := #[
  13,6,11,12,10,9,5,4,3,2,8,1,7,0
]
def img72 : Array ℕ := #[
  1,3,7,0,8,2,4,5,6,9,10,13,11,12
]
def img73 : Array ℕ := #[
  12,9,4,8,0,13,7,6,5,3,11,2,10,1
]
def img74 : Array ℕ := #[
  2,5,10,1,11,3,6,7,9,13,0,12,4,8
]
def img75 : Array ℕ := #[
  8,13,6,11,1,12,10,9,7,5,4,3,0,2
]
def img76 : Array ℕ := #[
  3,7,0,2,4,5,9,10,13,12,1,8,6,11
]
def img77 : Array ℕ := #[
  11,12,9,4,2,8,0,13,10,7,6,5,1,3
]
def img78 : Array ℕ := #[
  5,10,1,3,6,7,13,0,12,8,2,11,9,4
]
def img79 : Array ℕ := #[
  4,8,13,6,3,11,1,12,0,10,9,7,2,5
]
def img80 : Array ℕ := #[
  7,0,2,5,9,10,12,1,8,11,3,4,13,6
]
def img81 : Array ℕ := #[
  6,11,12,9,5,4,2,8,1,0,13,10,3,7
]
def img82 : Array ℕ := #[
  10,1,3,7,13,0,8,2,11,4,5,6,12,9
]
def img83 : Array ℕ := #[
  9,4,8,13,7,6,3,11,2,1,12,0,5,10
]
def images : Array (Array ℕ) := #[img0,img1,img2,img3,img4,img5,img6,img7,img8,img9,img10,img11,img12,img13,img14,img15,img16,img17,img18,img19,img20,img21,img22,img23,img24,img25,img26,img27,img28,img29,img30,img31,img32,img33,img34,img35,img36,img37,img38,img39,img40,img41,img42,img43,img44,img45,img46,img47,img48,img49,img50,img51,img52,img53,img54,img55,img56,img57,img58,img59,img60,img61,img62,img63,img64,img65,img66,img67,img68,img69,img70,img71,img72,img73,img74,img75,img76,img77,img78,img79,img80,img81,img82,img83]

abbrev G := Fin 84
abbrev Class := Fin 4
def rep (k : Class) : FixedPool.Index := ([1,4,6,13] : List FixedPool.Index)[k.val]!
def dual (g : G) := duals.getD g.val 0 == 1
def ar (g : G) (x : V) : V := (Fin.ofNat 21 (scales.getD g.val 0))*x+(Fin.ofNat 21 (rowOffsets.getD g.val 0))
def ac (g : G) (x : V) : V := (Fin.ofNat 21 (scales.getD g.val 0))*x+(Fin.ofNat 21 (colOffsets.getD g.val 0))
def point (g : G) (x y : V) : V × V := if dual g then (ar g y,ac g x) else (ar g x,ac g y)
def pull (g : G) (b : Box) : Box := if dual g then
  (univ.filter (fun x => ac g x ∈ b.2),univ.filter (fun y => ar g y ∈ b.1))
  else (univ.filter (fun x => ar g x ∈ b.1),univ.filter (fun y => ac g y ∈ b.2))
theorem pullHit (g : G) (b : Box) (x y : V) :
    hit (pull g b) x y ↔ hit b (point g x y).1 (point g x y).2 := by
  by_cases d : dual g=true <;> simp [pull,hit,point,d,and_comm]
theorem preserves : ∀ (g : G) (x y : V),bit (point g x y).1 (point g x y).2=bit x y := by
  intro g
  fin_cases g <;> decide +kernel
theorem pullLegal (g : G) (b : Box) (ok : legal b) : legal (pull g b) := by
  intro x hx y hy
  obtain ⟨hr,hc⟩ := (pullHit g b x y).mp ⟨hx,hy⟩
  rw [←preserves g x y]
  exact ok _ hr _ hc
theorem phaseLift : ∀ (g : G) (u : Phase),∃ v : Phase,∀x : V,
    ar g (x+step v)=ar g x+step u ∧ ac g (x+step v)=ac g x+step u := by
  intro g
  fin_cases g <;> decide +kernel
theorem pullOrbit (g : G) (b : Box) (x y : V) :
    Hit b (point g x y).1 (point g x y).2 → Hit (pull g b) x y := by
  rintro ⟨u,hu⟩
  obtain ⟨v,h⟩ := phaseLift g u
  refine ⟨v,(pullHit ..).mpr ?_⟩
  by_cases d : dual g=true <;> simpa [point,d,(h x).1,(h x).2,(h y).1,(h y).2] using hu
def dest (g : G) (i : FixedPool.Index) : FixedPool.Index :=
  Fin.ofNat 14 ((images.getD g.val #[]).getD i.val 0)
def row (i : FixedPool.Index) (v : V) := (FixedPool.rectRows.getD i.val 0).testBit v.val
def col (i : FixedPool.Index) (v : V) := (FixedPool.rectCols.getD i.val 0).testBit v.val
theorem axis : ∀(g : G) (i : FixedPool.Index) (x : V),
    row (dest g i) (ar g x)=(if dual g then col i x else row i x) ∧
    col (dest g i) (ac g x)=(if dual g then row i x else col i x) := by
  intro g
  fin_cases g <;> decide +kernel
theorem movesStar (g : G) (i : FixedPool.Index) (x y : V) :
    FixedPool.contains (dest g i) (point g x y).1 (point g x y).2 ↔ FixedPool.contains i x y := by
  change (row _ _=true ∧ col _ _=true) ↔ row i x=true ∧ col i y=true
  by_cases d : dual g=true <;> simp [point,d,(axis g i _).1,(axis g i _).2,and_comm]
def sel (i j : FixedPool.Index) := selections.getD (14*i.val+j.val) 0
def action (i j : FixedPool.Index) := Fin.ofNat 84 (sel i j / 4)
def which (i j : FixedPool.Index) := Fin.ofNat 4 (sel i j % 4)
theorem pairTable : ∀i j : FixedPool.Index,
    let g := action i j
    let k := which i j
    (i=dest g 0 ∨ i=dest g (rep k)) ∧ (j=dest g 0 ∨ j=dest g (rep k)) := by decide +kernel
theorem classify (i j : FixedPool.Index) : ∃ (g : G) (k : Class),∀ x y,
    (FixedPool.contains i (point g x y).1 (point g x y).2 ∨ FixedPool.contains j (point g x y).1 (point g x y).2) →
    FixedPool.contains 0 x y ∨ FixedPool.contains (rep k) x y := by
  let g := action i j
  let k := which i j
  refine ⟨g,k,?_⟩
  obtain ⟨hi,hj⟩ := pairTable i j
  intro x y h
  have transfer (u : FixedPool.Index) (eq : u=dest g 0 ∨ u=dest g (rep k))
      (h : FixedPool.contains u (point g x y).1 (point g x y).2) :
      FixedPool.contains 0 x y ∨ FixedPool.contains (rep k) x y := by
    rcases eq with rfl|rfl
    · exact Or.inl ((movesStar ..).mp h)
    · exact Or.inr ((movesStar ..).mp h)
  exact h.elim (transfer _ hi) (transfer _ hj)
#print axioms classify
end Checkpoint134.Actions
