import FullRowFloor

namespace Checkpoint132.Induced
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Prune
open PEqualNP.Outside.L_meta_3004_aux.Controls

abbrev Slot (t : ℕ) := {v : V // t.testBit v.val=true}
def adj {t : ℕ} (v w : Slot t) : Prop := G.Adj v.val w.val
instance {t} (v w : Slot t) : Decidable (adj v w) := inferInstanceAs (Decidable (G.Adj _ _))
def accepts {t : ℕ} (z : Slot t→Bool) := ∃ a b,adj a b ∧ z a=true ∧ z b=true
instance {t} (z : Slot t→Bool) : Decidable (accepts z) := by unfold accepts; infer_instance

abbrev Yes (t : ℕ) := {z : Slot t→Bool // accepts z}
abbrev No (t : ℕ) := {z : Slot t→Bool // ¬accepts z}
def pv {t} (z : Yes t) (a : Slot t) : Prop := z.val a=true
def nv {t} (z : No t) (a : Slot t) : Prop := z.val a=true
def Floor (t k : ℕ) : Prop := ∀ gs : List (Binary.Tree (Slot t)), ∀ e, Built gs → Ready gs e →
  Fits pv nv e → k≤gs.length

private theorem loop {t} (v : Slot t) : ¬adj v v := G.loopless.irrefl _
private theorem sym {t} {v w : Slot t} (h : adj v w) : adj w v := h.symm

def mark {t} (a : Slot t) (v : Slot t) := decide (v=a)
def put {t} (a : Slot t) (z : Slot t→Bool) (v : Slot t) := decide (v=a) || z v

theorem singleNo {t} (u : Slot t) : ¬accepts (mark u) := by
  rintro ⟨a,b,edge,ha,hb⟩
  obtain rfl : a=u := by simpa [mark] using ha
  obtain rfl : b=a := by simpa [mark] using hb
  exact loop _ edge

private theorem pairNo {t} (u w : Slot t) (away : ¬adj u w) : ¬accepts (put w (mark u)) := by
  rintro ⟨a,b,edge,ha,hb⟩
  obtain aa : a=w ∨ a=u := by simpa [mark,put] using ha
  obtain bb : b=w ∨ b=u := by simpa [mark,put] using hb
  rcases aa with rfl|rfl <;> rcases bb with rfl|rfl
  · exact loop _ edge
  · exact away (sym edge)
  · exact away edge
  · exact loop _ edge

theorem noLeaf {t} (v : Slot t) : ¬Fits pv nv (.leaf v) := by
  intro h
  exact h.2 ⟨mark v,singleNo v⟩ (by simp [Binary.Tree.eval,nv,mark])

theorem used {t} {e : Binary.Tree (Slot t)} (ok : Fits pv nv e) {v u : Slot t} (edge : adj v u) :
    v∈e.vars := by
  let low := mark u
  let high := put v low
  have yes : accepts high := ⟨v,u,edge,by simp [high,put],by simp [high,low,put,mark]⟩
  apply mandatory ok v ⟨high,yes⟩ ⟨low,singleNo u⟩
  intro w wv
  simp [pv,nv,high,put,wv]

theorem inputFloor {t k : ℕ} (each : ∀ v : Slot t,∃ u,adj v u) (n : k+1≤Fintype.card (Slot t)) : Floor t k := by
  intro gs e hb hr ok
  have all : e.vars=univ := by
    apply eq_univ_of_forall
    intro v
    obtain ⟨u,edge⟩ := each v
    exact used ok edge
  have size := (inputBudget hb hr).1
  rw [all,card_univ] at size
  omega

def witness {t} (op : Bool) (x y v u : Slot t) : Prop :=
  adj v u ∧ (v=x → if op then ¬adj u y else u≠y) ∧ (v=y → if op then ¬adj u x else u≠x)
instance {t} (op : Bool) (x y v u : Slot t) : Decidable (witness op x y v u) := by unfold witness; infer_instance

/-- A vertex is necessary below a cut if the two rows differ only there and the fresh wire
cannot distinguish their signs. The witness may use the other operand itself for OR. -/
theorem cutUsed {t} (op : Bool) (x y v u : Slot t) (xy : x≠y) (w : witness op x y v u)
    {e : Binary.Tree (Option (Slot t))}
    (ok : Fits (fun z => extend op x y (pv z)) (fun z => extend op x y (nv z)) e) : some v∈e.vars := by
  obtain ⟨edge,whenX,whenY⟩ := w
  let low (a : Slot t) := mark u a || (op && ((decide (v=x) && mark y a) || (decide (v=y) && mark x a)))
  let high := put v low
  have yes : accepts high := ⟨v,u,edge,by simp [high,put],by simp [high,put,low,mark]⟩
  have no : ¬accepts low := by
    by_cases vx : v=x
    · have vy : v≠y := fun h => xy (vx.symm.trans h)
      cases op
      · simpa [low] using singleNo u
      · have away : ¬adj u y := whenX vx
        have eq : low=put y (mark u) := by funext a; simp [low,put,mark,vx,xy,Bool.or_comm]
        exact eq ▸ pairNo u y away
    · by_cases vy : v=y
      · cases op
        · simpa [low] using singleNo u
        · have away : ¬adj u x := whenY vy
          have eq : low=put x (mark u) := by funext a; simp [low,put,mark,vy,Ne.symm xy,Bool.or_comm]
          exact eq ▸ pairNo u x away
      · simpa [low,vx,vy] using singleNo u
  apply mandatory ok (some v) ⟨high,yes⟩ ⟨low,no⟩
  rintro (_|a) different
  · by_cases vx : v=x
    · cases op
      · have uy : u≠y := whenX vx
        have yv : y≠v := fun h => xy (vx.symm.trans h.symm)
        simp [extend,pv,nv,high,put,low,mark,uy.symm,yv]
      · simp [extend,pv,nv,low,mark,vx]
    · by_cases vy : v=y
      · cases op
        · have ux : u≠x := whenY vy
          simp [extend,pv,nv,high,put,low,mark,Ne.symm ux,Ne.symm vx]
        · simp [extend,pv,nv,low,mark,vy]
      · cases op <;> simp [extend,pv,nv,high,put,Ne.symm vx,Ne.symm vy]
  · have av : a≠v := fun eq => different (congrArg some eq)
    simp [extend,pv,nv,high,put,av]
#print axioms inputFloor
#print axioms cutUsed
end Checkpoint132.Induced
