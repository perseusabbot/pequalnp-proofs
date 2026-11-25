import ConstantPruning
import CherryBound

namespace Checkpoint130.Cut
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint126.Cherry Checkpoint130.Prune

variable {A B I J K L : Type} [DecidableEq A] [DecidableEq B]

def Fits (p : I→A→Prop) (n : J→A→Prop) (e : Binary.Tree A) : Prop :=
  (∀ i,e.eval (p i)) ∧ ∀ j,¬e.eval (n j)

def extend (op : Bool) (x y : A) (ρ : A→Prop) : Option A→Prop
  | some a => ρ a
  | none => if op then ρ x ∨ ρ y else ρ x ∧ ρ y

/-- If two rows can only be distinguished by a specified label, a separating
monotone circuit must read that label. -/
theorem mandatory {p : I→A→Prop} {n : J→A→Prop} {e : Binary.Tree A} (ok : Fits p n e)
    (a : A) (i : I) (j : J) (unique : ∀ b,b≠a → p i b → n j b) : a∈e.vars := by
  by_contra missing
  exact ok.2 j (e.mono (fun b hb => unique b (fun eq => missing (eq ▸ hb))) (ok.1 i))

/-- Cutting an occurring bottom gate pays one gate and preserves the exact row signs.
The new free wire occurs in the continuation. -/
theorem split {p : I→A→Prop} {n : J→A→Prop} {book : List (Binary.Tree A)} (built : Built book)
    {e : Binary.Tree A} (ready : Ready book e) (ok : Fits p n e) {op x y}
    (occurs : Binary.Tree.gate op (.leaf x) (.leaf y)∈nodes e) :
    ∃ gs : List (Binary.Tree (Option A)), ∃ t, Built gs ∧ Ready gs t ∧ gs.length+1≤book.length ∧
      none∈t.vars ∧ Fits (fun i => extend op x y (p i)) (fun j => extend op x y (n j)) t := by
  let u : Binary.Tree A := .gate op (.leaf x) (.leaf y)
  obtain ⟨good,available⟩ := covered u some none built
  have shorter := oneLess some none (listed built e ready u occurs)
  have eq (ρ : A→Prop) : (extend op x y ρ) none ↔ u.eval (fun a => extend op x y ρ (some a)) := by
    cases op <;> rfl
  have same (ρ : A→Prop) := cutTruth u some none (extend op x y ρ) (eq ρ) e
  exact ⟨_,_,good,available _ ready,shorter,fresh some none _ occurs,
    fun i => (same (p i)).mpr (ok.1 i),fun j h => ok.2 j ((same (n j)).mp h)⟩

/-- Removing repeated-operand gates yields a distinct-operand bottom gate
with one fewer gate available in the continuation. -/
theorem firstDistinct {p : I→A→Prop} {n : J→A→Prop} (noLeaf : ∀ a,¬Fits p n (.leaf a))
    {book : List (Binary.Tree A)} (built : Built book) {e : Binary.Tree A}
    (ready : Ready book e) (ok : Fits p n e) :
    ∃ op x y,x≠y ∧ ∃ gs : List (Binary.Tree (Option A)), ∃ t,
      Built gs ∧ Ready gs t ∧ gs.length+1≤book.length ∧ none∈t.vars ∧
      Fits (fun i => extend op x y (p i)) (fun j => extend op x y (n j)) t := by
  classical
  generalize hn : book.length=k
  induction k using Nat.strong_induction_on generalizing book e with
  | ind k ih =>
    rcases bottom e with ⟨a,rfl⟩|⟨op,x,y,used⟩
    · exact False.elim (noLeaf a ok)
    by_cases eq : x=y
    · subst y
      let u : Binary.Tree A := .gate op (.leaf x) (.leaf x)
      obtain ⟨good,go⟩ := covered u id x built
      have shorter := oneLess id x (listed built e ready u used)
      have same (ρ : A→Prop) : (cut u id x e).eval ρ ↔ e.eval ρ := by
        apply cutTruth u id x ρ _ e
        cases op <;> simp [u,Binary.Tree.eval]
      have fits : Fits p n (cut u id x e) :=
        ⟨fun i => (same (p i)).mpr (ok.1 i),fun j h => ok.2 j ((same (n j)).mp h)⟩
      obtain ⟨q,a,b,ne,gs,t,hb,hr,le,hf,hc⟩ := ih _ (by omega) good (go e ready) fits rfl
      exact ⟨q,a,b,ne,gs,t,hb,hr,by omega,hf,hc⟩
    · obtain ⟨gs,t,hb,hr,le,hf,hc⟩ := split built ready ok used
      exact ⟨op,x,y,eq,gs,t,hb,hr,by omega,hf,hc⟩

/-- A label bypasses a bottom gate whenever it is a different input from both
operands. Such a label remains present after the cut. -/
theorem untouched (op : Bool) {a b v : A} (va : v≠a) (vb : v≠b) (e : Binary.Tree A) :
    some v∈(cut (.gate op (.leaf a) (.leaf b)) some none e).vars ↔ v∈e.vars := by
  induction e with
  | leaf x => simp [cut]
  | gate q x y ix iy =>
    by_cases same : Binary.Tree.gate q x y=.gate op (.leaf a) (.leaf b)
    · cases same; simp [cut,va,vb]
    · simp [cut,same,ix,iy]

omit [DecidableEq B] in
/-- On each local positive row a replacement may raise a column. On each local
negative row it may lower it. All columns use the same chosen lift of that row. -/
theorem signedProjection {p : I→A→Prop} {n : J→A→Prop} {book : List (Binary.Tree A)} (built : Built book)
    {e : Binary.Tree A} (ready : Ready book e) (ok : Fits p n e)
    (f : A→Value B) (pos : K→B→Prop) (neg : L→B→Prop) (px : K→I) (nx : L→J)
    (hi : ∀ i a,p (px i) a → (f a).truth (pos i))
    (lo : ∀ j a,(f a).truth (neg j) → n (nx j) a)
    (positive : K) (negative : L) (fixed : Finset A)
    (needed : ∀ a∈fixed,a∈e.vars ∧ (f a).port=none) :
    ∃ gs : List (Binary.Tree B), ∃ t, Built gs ∧ Ready gs t ∧ Fits pos neg t ∧
      gs.length+fixed.card≤book.length := by
  have yes (i : K) := (semantics f (pos i) e).mpr (e.mono (fun a _ => hi i a) (ok.1 (px i)))
  have no (j : L) : ¬(specialize f e).truth (fun t => t.eval (neg j)) := by
    intro h
    exact ok.2 (nx j) (e.mono (fun a _ => lo j a) ((semantics f (neg j) e).mp h))
  cases hv : specialize f e with
  | bit b =>
    have on := yes positive
    have off := no negative
    simp only [hv,Value.truth] at on off
    exact False.elim (off on)
  | wire t =>
    have live : reduce f e=some t := by simp [reduce,hv,Value.port]
    have size := cost f built ready live
    have bound := card_le_card (show fixed⊆e.vars.filter (fun a => (f a).port=none) from
      fun a ha => mem_filter.mpr (needed a ha))
    obtain ⟨good,pruned⟩ := library f built
    exact ⟨_,t,good,pruned e ready t live,⟨fun i => by simpa [hv,Value.truth] using yes i,
      fun j => by simpa [hv,Value.truth] using no j⟩,by omega⟩

#print axioms mandatory
#print axioms split
#print axioms firstDistinct
#print axioms untouched
#print axioms signedProjection
end Checkpoint130.Cut
