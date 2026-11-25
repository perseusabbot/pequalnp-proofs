import BinaryBudget

namespace Checkpoint126.Cherry
open Finset Checkpoint125 Checkpoint125.Binary
variable {A B : Type} [DecidableEq A] [DecidableEq B]

def nodes : Binary.Tree A→List (Binary.Tree A)
  | .leaf _ => []
  | .gate op a b => .gate op a b::(nodes a++nodes b)

omit [DecidableEq A] in
theorem listed {gs : List (Binary.Tree A)} (h : Built gs) :
    ∀ e, Ready gs e → ∀ t∈nodes e, t∈gs := by
  induction gs with
  | nil =>
    rintro e (⟨x,rfl⟩|bad) <;> simp [nodes] at *
  | cons g gs ih =>
    obtain ⟨prev,op,a,b,rfl,ra,rb⟩ := h
    rintro e (⟨x,rfl⟩|he) t ht
    · simp [nodes] at ht
    rcases List.mem_cons.mp he with rfl|old
    · rcases List.mem_cons.mp ht with rfl|sub
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ ((List.mem_append.mp sub).elim (ih prev a ra t) (ih prev b rb t))
    · exact List.mem_cons_of_mem _ (ih prev e (Or.inr old) t ht)

omit [DecidableEq A] in
theorem bottom (e : Binary.Tree A) : (∃ x,e=Binary.Tree.leaf x) ∨
    ∃ op x y, Binary.Tree.gate op (.leaf x) (.leaf y)∈nodes e := by
  induction e with
  | leaf a => exact Or.inl ⟨a,rfl⟩
  | gate op a b ia ib =>
    right
    rcases ia with ⟨x,rfl⟩|⟨q,x,y,h⟩
    · rcases ib with ⟨y,rfl⟩|⟨q,u,v,h⟩
      · exact ⟨op,x,y,List.mem_cons_self ..⟩
      · exact ⟨q,u,v,List.mem_cons_of_mem _ (List.mem_append_right _ h)⟩
    · exact ⟨q,x,y,List.mem_cons_of_mem _ (List.mem_append_left _ h)⟩

def cut (n : Binary.Tree A) (f : A→B) (z : B) : Binary.Tree A→Binary.Tree B
  | .leaf x => .leaf (f x)
  | .gate op a b => if Binary.Tree.gate op a b=n then .leaf z else .gate op (cut n f z a) (cut n f z b)

def upper (n : Binary.Tree A) (f : A→B) (z : B) (book : List (Binary.Tree A)) :=
  (book.filter fun g => g != n).map (cut n f z)

omit [DecidableEq B] in
theorem covered (n : Binary.Tree A) (f : A→B) (z : B) {book : List (Binary.Tree A)} (h : Built book) :
    Built (upper n f z book) ∧ ∀ e, Ready book e → Ready (upper n f z book) (cut n f z e) := by
  induction book with
  | nil =>
    refine ⟨trivial,?_⟩
    rintro e (⟨x,rfl⟩|bad)
    · exact Or.inl ⟨f x,rfl⟩
    · simp at bad
  | cons g gs ih =>
    obtain ⟨prev,op,a,b,rfl,ra,rb⟩ := h
    obtain ⟨ok,old⟩ := ih prev
    by_cases eq : Binary.Tree.gate op a b=n
    · have same : upper n f z (.gate op a b::gs)=upper n f z gs := by simp [upper,eq]
      rw [same]
      refine ⟨ok,?_⟩
      rintro e (⟨x,rfl⟩|mem)
      · exact Or.inl ⟨_,rfl⟩
      · rcases List.mem_cons.mp mem with rfl|prev
        · exact Or.inl ⟨z,by simp [cut,eq]⟩
        · exact old e (Or.inr prev)
    · have new : upper n f z (.gate op a b::gs)=
          .gate op (cut n f z a) (cut n f z b)::upper n f z gs := by simp [upper,cut,eq]
      rw [new]
      refine ⟨⟨ok,op,_,_,rfl,old _ ra,old _ rb⟩,?_⟩
      rintro e (⟨x,rfl⟩|mem)
      · exact Or.inl ⟨_,rfl⟩
      · rcases List.mem_cons.mp mem with rfl|prev
        · exact Or.inr (by simp [cut,eq])
        · exact (old e (Or.inr prev)).imp_right (List.mem_cons_of_mem _)

omit [DecidableEq B] in
theorem cutTruth (n : Binary.Tree A) (f : A→B) (z : B) (ρ : B→Prop)
    (eq : ρ z ↔ n.eval (fun a => ρ (f a))) (e : Binary.Tree A) :
    (cut n f z e).eval ρ ↔ e.eval (fun a => ρ (f a)) := by
  induction e with
  | leaf a => rfl
  | gate op a b ia ib =>
    by_cases hn : Binary.Tree.gate op a b=n
    · rw [cut,ite_eq_left hn]
      exact hn ▸ eq
    · cases op <;> simp [cut,hn,Binary.Tree.eval,ia,ib]

theorem fresh {n : Binary.Tree A} (f : A→B) (z : B) (e : Binary.Tree A) (member : n∈nodes e) :
    z∈(cut n f z e).vars := by
  induction e with
  | leaf a => simp [nodes] at member
  | gate op a b ia ib =>
    by_cases h : Binary.Tree.gate op a b=n
    · simp [cut,h]
    · rcases List.mem_cons.mp member with eq|sub
      · exact False.elim (h eq.symm)
      · simp only [cut,ite_eq_right h,Binary.Tree.gateVars,mem_union]
        exact (List.mem_append.mp sub).imp ia ib

omit [DecidableEq B] in
theorem oneLess {n : Binary.Tree A} (f : A→B) (z : B) {gs} (mem : n∈gs) :
    (upper n f z gs).length < gs.length := by
  simp only [upper,List.length_map]
  have sub : (gs.filter (fun t => t != n)).Sublist gs := List.filter_sublist
  by_contra! le
  have eq := sub.eq_of_length (Nat.le_antisymm sub.length_le le)
  have hm : n∈(gs.filter fun t => t != n) := by rw [eq]; exact mem
  simp at hm

/-- The function can distinguish the variable x with a second variable y
held at either specified value. For x=y, only the unconstrained test is needed. -/
def Robust (C : Finset A) (F : (A→Bool)→Prop) :=
  ∀ x∈C, ∀ y : A, ∀ h : Bool, ∃ a b : A→Bool,
    F a ∧ ¬F b ∧ (∀ u, u≠x → a u=b u) ∧ (y≠x → a y=h ∧ b y=h)

private theorem need (C : Finset A) {F : (A→Bool)→Prop} (robust : Robust C F)
    (op : Bool) (x y : A) (diff : x≠y) (e : Binary.Tree (Option A))
    (truth : ∀ a : A→Bool, e.eval (fun k => match k with
      | some v => a v=true
      | none => (if op then a x || a y else a x && a y)=true) ↔ F a) :
    C.image some ⊆ e.vars := by
  rintro _ hv
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
  by_contra missing
  let v := if u=x then y else x
  obtain ⟨a,b,yes,no,apart,fixed⟩ := robust u hu v op
  have neq : v≠u := by by_cases h : u=x <;> simp [v,h] <;> tauto
  obtain ⟨av,bv⟩ := fixed neq
  have same : (if op then a x || a y else a x && a y)=(if op then b x || b y else b x && b y) := by
    by_cases h : u=x
    · simp [v,h] at av bv
      cases op <;> simp_all
    · simp [v,h] at av bv
      cases op <;> simp_all
  apply no
  apply (truth b).mp
  apply e.mono _ ((truth a).mpr yes)
  rintro (_|z) hz h
  · exact same ▸ h
  · change b z=true
    change a z=true at h
    exact (apart z (fun eq => missing (eq ▸ hz))).symm.trans h

/-- If every variable in C is essential after fixing any other variable to
either constant, at least |C|+1 binary AND/OR gates are required. -/
theorem lower {C : Finset A} (two : 2≤C.card) {F : (A→Bool)→Prop} (robust : Robust C F)
    {book : List (Binary.Tree A)} (built : Built book) {e : Binary.Tree A} (ready : Ready book e)
    (truth : ∀ a : A→Bool, e.eval (fun v => a v=true) ↔ F a) : C.card+1≤book.length := by
  classical
  generalize hn : book.length=n
  induction n using Nat.strong_induction_on generalizing book e with
  | ind n ih =>
    rcases bottom e with ⟨v,rfl⟩|⟨op,x,y,member⟩
    · have other : ∃ x∈C,x≠v := by
        by_contra! empty
        have sub : C⊆{v} := fun x hx => mem_singleton.mpr (empty x hx)
        have := card_le_card sub
        simp at this
        omega
      obtain ⟨x,hx,ne⟩ := other
      obtain ⟨a,b,yes,no,apart,_⟩ := robust x hx v false
      have av : a v=true := (truth a).mpr yes
      exact False.elim (no ((truth b).mp ((apart v ne.symm).symm.trans av)))
    · let u : Binary.Tree A := .gate op (.leaf x) (.leaf y)
      have used : u∈book := listed built e ready u member
      by_cases eq : x=y
      · subst y
        obtain ⟨ok,go⟩ := covered u id x built
        have len := oneLess id x used
        have ev (a : A→Bool) : (cut u id x e).eval (fun v => a v=true) ↔ F a := by
          have same : (a x=true) ↔ u.eval (fun v => a (id v)=true) := by cases op <;> simp [u,Binary.Tree.eval]
          exact (cutTruth u id x (fun v => a v=true) same e).trans (truth a)
        exact (ih _ (by omega) ok (go _ ready) ev rfl).trans (by omega)
      · let f : A→Option A := some
        obtain ⟨ok,go⟩ := covered u f none built
        have len := oneLess f none used
        have cap := (inputBudget ok (go e ready)).1
        have extra := fresh f none e member
        have must := need C robust op x y eq (cut u f none e) (by
          intro a
          let ρ : Option A→Prop := fun k => match k with
            | some v => a v=true
            | none => (if op then a x || a y else a x && a y)=true
          have same : ρ none ↔ u.eval (fun v => ρ (f v)) := by cases op <;> simp [ρ,u,Binary.Tree.eval,f]
          exact (cutTruth u f none ρ same e).trans (truth a))
        have inc := card_le_card (insert_subset extra must)
        have sz : (insert none (C.image some)).card=C.card+1 := by simp [card_image_of_injective _ (Option.some_injective A)]
        change (insert none (C.image some)).card≤(cut u f none e).vars.card at inc
        rw [sz] at inc
        omega

#print axioms lower
end Checkpoint126.Cherry
