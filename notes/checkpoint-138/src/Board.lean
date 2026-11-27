import PEqualNP.Outside.L_meta_9338

namespace Checkpoint138

open PEqualNP.Outside.L_meta_9338 Finset

abbrev Cell := V × V
abbrev Inc (x : Cell) (h : H) := x.1 ∈ (oval h).1 ∧ x.2 ∈ (oval h).2

def moveCell (g : G) (x : Cell) : Cell := (permR g x.1,permC g x.2)

def moveCells (w : List G) (x : Cell) : Cell := w.foldl (fun y g => moveCell g y) x

theorem moveInc (g : G) (x : Cell) (h : H) : Inc (moveCell g x) (act g h) ↔ Inc x h := by
  have hr : Function.Injective (permR g) := Finite.injective_iff_surjective.mpr (genFacts g).2.1
  have hc : Function.Injective (permC g) := Finite.injective_iff_surjective.mpr (genFacts g).2.2
  unfold Inc moveCell
  rw [← genOval g h]
  simp [moved,hr.mem_finset_image,hc.mem_finset_image]

theorem walkInc (w : List G) (x : Cell) (h : H) : Inc (moveCells w x) (walk w h) ↔ Inc x h := by
  induction w generalizing x h with
  | nil => rfl
  | cons g t ih => exact (ih (moveCell g x) (act g h)).trans (moveInc g x h)

private theorem walkBit (w : List G) (x : Cell) :
    bit (moveCells w x).1 (moveCells w x).2 = bit x.1 x.2 := by
  induction w generalizing x with
  | nil => rfl
  | cons g t ih => exact (ih (moveCell g x)).trans ((genFacts g).1 x.1 x.2)

set_option maxHeartbeats 0 in
private theorem zeroBase : ∀ z : Cell, Inc z 0 → bit z.1 z.2 = false := by decide +kernel

theorem zeroOfInc {x : Cell} {h : H} (yes : Inc x h) : bit x.1 x.2 = false := by
  let w := firstMoves[h.val]!
  have moved := (walkInc w x h).mpr yes
  rw [show walk w h = 0 from startFacts.1 h] at moved
  exact (walkBit w x).symm.trans (zeroBase (moveCells w x) moved)

/-- Four off-diagonal tests inside the specified rectangle, with all four alternatives through x. -/
def Pattern (h : H) (x : Cell) :=
  ∃ (ys : Fin 4 → Cell) (hs : Fin 4 → H), (∀ i, Inc (ys i) h) ∧
    (∀ i, Inc x (hs i)) ∧ ∀ i j, Inc (ys i) (hs j) ↔ i ≠ j

theorem transportPattern (w : List G) {r : H} {x : Cell} (p : Pattern r x) :
    Pattern (walk w r) (moveCells w x) := by
  obtain ⟨ys,hs,inside,through,cross⟩ := p
  exact ⟨fun i => moveCells w (ys i),fun j => walk w (hs j),
    fun i => (walkInc ..).mpr (inside i),fun j => (walkInc ..).mpr (through j),
    fun i j => (walkInc ..).trans (cross i j)⟩

def contained (a b c d : Nat) : Prop := (a &&& b &&& c &&& d) = (a &&& b &&& c)
instance (a b c d : Nat) : Decidable (contained a b c d) := inferInstanceAs (Decidable (_ = _))

def redundant (a b c d : Nat) := contained a b c d ∨ contained a b d c ∨
  contained a c d b ∨ contained b c d a
instance (a b c d : Nat) : Decidable (redundant a b c d) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem passBit {a b c d i : Nat} (h : contained a b c d)
    (ha : a.testBit i = true) (hb : b.testBit i = true) (hc : c.testBit i = true) :
    d.testBit i = true := by
  have value := congrArg (fun n : Nat => n.testBit i) h
  simpa [Nat.testBit_and,ha,hb,hc] using value

#print axioms zeroOfInc
#print axioms walkInc
#print axioms transportPattern
#print axioms passBit

end Checkpoint138
