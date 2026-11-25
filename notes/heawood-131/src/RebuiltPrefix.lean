import CutTransfer

namespace Checkpoint131.Rebuild
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Prune

variable {A B I J K L : Type}

def graft (f : A → Binary.Tree B) : Binary.Tree A → Binary.Tree B
  | .leaf a => f a
  | .gate op a b => .gate op (graft f a) (graft f b)

theorem graftTruth (f : A → Binary.Tree B) (ρ : B → Prop) (e : Binary.Tree A) :
    (graft f e).eval ρ ↔ e.eval (fun a => (f a).eval ρ) := by
  induction e with
  | leaf a => rfl
  | gate op a b ia ib => cases op <;> simp [graft,Binary.Tree.eval,ia,ib]

theorem graftReady (f : A → Binary.Tree B) {base : List (Binary.Tree B)} (available : ∀ a,Ready base (f a))
    {book : List (Binary.Tree A)} {e : Binary.Tree A} (ready : Ready book e) :
    Ready (book.map (graft f) ++ base) (graft f e) := by
  rcases ready with ⟨a,rfl⟩ | old
  · rcases available a with lit | used
    · exact Or.inl lit
    · exact Or.inr (List.mem_append_right _ used)
  · exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨_,old,rfl⟩))

theorem graftBuilt (f : A → Binary.Tree B) {base : List (Binary.Tree B)} (baseBuilt : Built base)
    (available : ∀ a,Ready base (f a)) {book : List (Binary.Tree A)} (built : Built book) :
    Built (book.map (graft f) ++ base) := by
  induction book with
  | nil => exact baseBuilt
  | cons e book ih =>
    obtain ⟨prev,op,a,b,rfl,ra,rb⟩ := built
    exact ⟨ih prev,op,_,_,rfl,graftReady f available ra,graftReady f available rb⟩

/-- A shared prefix can be rebuilt once. Signed replacements may name any
wire in that prefix. Every distinct constant label used by the suffix saves a gate. -/
theorem rebuiltProjection [DecidableEq A]
    {p : I→A→Prop} {n : J→A→Prop} {book : List (Binary.Tree A)} (built : Built book)
    {e : Binary.Tree A} (ready : Ready book e) (ok : Fits p n e)
    {base : List (Binary.Tree B)} (baseBuilt : Built base)
    (f : A → Value {w : Binary.Tree B // Ready base w})
    (pos : K→B→Prop) (neg : L→B→Prop) (px : K→I) (nx : L→J)
    (hi : ∀ i a,p (px i) a → (f a).truth (fun w => w.val.eval (pos i)))
    (lo : ∀ j a,(f a).truth (fun w => w.val.eval (neg j)) → n (nx j) a)
    (positive : K) (negative : L) (fixed : Finset A)
    (needed : ∀ a∈fixed,a∈e.vars ∧ (f a).port=none) :
    ∃ gs : List (Binary.Tree B), ∃ t, Built gs ∧ Ready gs t ∧ Fits pos neg t ∧
        gs.length+fixed.card ≤ book.length+base.length := by
  obtain ⟨qs,t,hb,hr,hf,hs⟩ := signedProjection built ready ok f
    (fun i w => w.val.eval (pos i)) (fun j w => w.val.eval (neg j)) px nx hi lo
    positive negative fixed needed
  let cast : {w : Binary.Tree B // Ready base w} → Binary.Tree B := Subtype.val
  have av (w) : Ready base (cast w) := w.property
  refine ⟨_,_,graftBuilt cast baseBuilt av hb,graftReady cast av hr,?_,?_⟩
  · exact ⟨fun i => (graftTruth cast (pos i) t).mpr (hf.1 i),
      fun j h => hf.2 j ((graftTruth cast (neg j) t).mp h)⟩
  · simp only [List.length_append,List.length_map]
    omega

#print axioms graftTruth
#print axioms graftReady
#print axioms graftBuilt
#print axioms rebuiltProjection
end Checkpoint131.Rebuild
