import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

namespace Checkpoint133.Plane

abbrev V := Fin 21
abbrev H := Fin 7
abbrev Box := Finset V × Finset V

def lines : List ℕ := [1179809,262467,524934,1049868,2585,5170,10340,20680,41360,82720,165440,330880,661760,1323520,549889,1099778,102405,204810,409620,819240,1638480]
def rowWord (i : V) := 2097151 ^^^ lines.getD i.val 0
def colWord (j : V) := [2015212,1933273,1769395,1441639,786127,1572254,1047357,2094714,2092277,2087403,2077655,2058159,2019167,1941183,1785215,1473279,849407,1698814,1300477,503803,1007606].getD j.val 0
def zeroCell (i j : V) := (rowWord i).testBit j.val = true
instance (i j) : Decidable (zeroCell i j) := inferInstanceAs (Decidable (_ = true))
def move (q : H) (i : V) : V := ⟨(i.val+3*q.val)%21, Nat.mod_lt _ (by decide)⟩

theorem moveZero : ∀ i,move 0 i=i := by decide +kernel
theorem moveAdd : ∀ q h i,move q (move h i)=move (q+h) i := by
  intro q h
  fin_cases q <;> fin_cases h <;> decide +kernel
theorem periodic : ∀ q i j,zeroCell (move q i) (move q j) ↔ zeroCell i j := by
  intro q i
  fin_cases q <;> fin_cases i <;> decide +kernel
theorem column : ∀ i j,(colWord j).testBit i.val=true ↔ zeroCell i j := by
  intro i
  fin_cases i <;> decide +kernel
theorem allBits : ∀ i : V,(2097151 : ℕ).testBit i.val=true := by decide +kernel

def Good (b : Box) := ∀ i∈b.1,∀ j∈b.2,zeroCell i j
def Covers (b : Box) (i j : V) := ∃ q : H,move q i∈b.1 ∧ move q j∈b.2
instance (b : Box) (i j : V) : Decidable (Covers b i j) := by unfold Covers; infer_instance

def turn (q : H) (b : Box) : Box :=
  (Finset.univ.filter fun i => move q i∈b.1, Finset.univ.filter fun j => move q j∈b.2)
theorem memLeft (q : H) (b : Box) (i : V) : i∈(turn q b).1 ↔ move q i∈b.1 := by simp [turn]
theorem memRight (q : H) (b : Box) (i : V) : i∈(turn q b).2 ↔ move q i∈b.2 := by simp [turn]
theorem turnGood {b : Box} (h : Good b) (q : H) : Good (turn q b) :=
  fun i hi j hj => (periodic q i j).mp (h _ ((memLeft ..).mp hi) _ ((memRight ..).mp hj))
theorem turnCover (q : H) (b : Box) (i j : V) : Covers (turn q b) i j ↔ Covers b i j := by
  constructor
  · rintro ⟨h,a,c⟩
    exact ⟨q+h,moveAdd q h i ▸ (memLeft ..).mp a,moveAdd q h j ▸ (memRight ..).mp c⟩
  · rintro ⟨h,a,c⟩
    refine ⟨h-q,(memLeft ..).mpr ?_,(memRight ..).mpr ?_⟩
    · rw [moveAdd,show q+(h-q)=h by abel]
      exact a
    · rw [moveAdd,show q+(h-q)=h by abel]
      exact c

def PairCovers (b d : Box) := ∀ i j,zeroCell i j → Covers b i j ∨ Covers d i j
structure Window where
  rs : ℕ
  cs : ℕ
  deriving Inhabited, DecidableEq

def free : Window := ⟨2097151,2097151⟩
def fits (s : Window) (b : Box) := (∀ i∈b.1,s.rs.testBit i.val=true) ∧ ∀ j∈b.2,s.cs.testBit j.val=true
theorem freeFits (b : Box) : fits free b := ⟨fun i _ => allBits i,fun j _ => allBits j⟩

def push (s : Window) (i j : V) : Window := ⟨s.rs &&& colWord j,s.cs &&& rowWord i⟩
def possible (s : Window) (q : H) (i j : V) : Prop :=
  (s ≠ free ∨ q=0) ∧ s.rs.testBit (move q i).val=true ∧ s.cs.testBit (move q j).val=true
instance (s q i j) : Decidable (possible s q i j) := by unfold possible; infer_instance

theorem pushFits {s b i j} (ok : fits s b) (g : Good b) (hi : i∈b.1) (hj : j∈b.2) : fits (push s i j) b := by
  constructor
  · intro x hx
    simp only [push,Nat.testBit_and,Bool.and_eq_true]
    exact ⟨ok.1 x hx,(column x j).mpr (g x hx j hj)⟩
  · intro y hy
    simp only [push,Nat.testBit_and,Bool.and_eq_true]
    exact ⟨ok.2 y hy,g i hi y hy⟩

theorem chooseMove {s b i j} (ok : fits s b) (g : Good b) (hit : Covers b i j) :
    ∃ q, possible s q i j ∧ ∃ b',Good b' ∧ fits (push s (move q i) (move q j)) b' ∧
      ∀ u v,Covers b u v → Covers b' u v := by
  obtain ⟨q,ri,cj⟩ := hit
  by_cases fresh : s=free
  · subst s
    let b' := turn q b
    have ri' : i∈b'.1 := (memLeft ..).mpr ri
    have cj' : j∈b'.2 := (memRight ..).mpr cj
    have good := turnGood g q
    refine ⟨0,⟨Or.inr rfl,allBits _,allBits _⟩,b',good,?_,fun u v => (turnCover q b u v).mpr⟩
    simpa only [moveZero] using pushFits (freeFits b') good ri' cj'
  · exact ⟨q,⟨Or.inl fresh,ok.1 _ ri,ok.2 _ cj⟩,b,g,pushFits ok g ri cj,fun _ _ h=>h⟩

def Dead (s t : Window) := ∀ b d, Good b → Good d → fits s b → fits t d → ¬PairCovers b d

theorem branch {s t i j} (zero : zeroCell i j)
    (left : ∀ q,possible s q i j → Dead (push s (move q i) (move q j)) t)
    (right : ∀ q,possible t q i j → Dead s (push t (move q i) (move q j))) : Dead s t := by
  intro b d gb gd fb fd cover
  rcases cover i j zero with l|r
  · obtain ⟨q,p,b',gb',fb',same⟩ := chooseMove fb gb l
    exact left q p b' d gb' gd fb' fd (fun u v z => (cover u v z).imp_left (same u v))
  · obtain ⟨q,p,d',gd',fd',same⟩ := chooseMove fd gd r
    exact right q p b d' gb gd' fb fd' (fun u v z => (cover u v z).imp_right (same u v))

#print axioms branch
end Checkpoint133.Plane
