import RegularBottom
import ResidualSemantics

namespace Checkpoint124.Library
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint124.Shapes

variable {X : Type}
abbrev Sources := Support 14
abbrev Graph := Finset (Sym2 (Fin 14))
def signal (xs : X → (Fin 14 → Bool)) (S : Sources) : Set X := {z | lit S (xs z)}

theorem signalUnion (xs : X → (Fin 14 → Bool)) (U V : Sources) :
    signal xs (U∪V)=signal xs U ∪ signal xs V := by
  ext z; simp [signal,lit,or_and_right,exists_or]

structure Scope (H : Graph) (k : ℕ) where
  q : Frame
  reachable : q∈frames k
  bank : List Sources
  size : bank.length=2*k
  regular : ∀ U∈bank, Regular H U

def Low {H k} (c : Scope H k) (xs : X → (Fin 14 → Bool)) (U : Sources) :=
  Regular H U ∨ Has (signal xs) c.bank c.q.pure (signal xs U)
def High {H k} (c : Scope H k) (xs : X → (Fin 14 → Bool)) (v : Set X) :=
  Has (signal xs) c.bank c.q.pool v
structure Extends {H k l} (xs : X → (Fin 14 → Bool)) (c : Scope H k) (d : Scope H l) : Prop where
  low : ∀ {U}, Low c xs U → Low d xs U
  high : ∀ {v}, High c xs v → High d xs v

variable {H : Graph} {k : ℕ} {xs : X → (Fin 14 → Bool)}
private def representative (H : Graph) (U : Sources) := if Regular H U then U else ∅
private theorem regRep (H : Graph) (U : Sources) : Regular H (representative H U) := by
  unfold representative
  split
  next h => exact h
  next => exact Or.inl (by simp)

private def enlarge (c : Scope H k) (U V : Sources) (p : Frame) (hp : p∈next k c.q) : Scope H (k+1) where
  q := p
  reachable := List.mem_flatMap.mpr ⟨c.q,c.reachable,hp⟩
  bank := c.bank++[representative H U,representative H V]
  size := by simp [c.size]; omega
  regular := by
    intro a ha
    rcases List.mem_append.mp ha with old|fresh
    · exact c.regular a old
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
      rcases fresh with rfl|rfl <;> exact regRep .. 

private theorem hasMono {read : Sources → Set X} {bank : List Sources} {P Q : List Form} {v : Set X}
    (h : Has read bank P v) (sub : ∀ f∈P, f∈Q) : Has read bank Q v := by
  obtain ⟨f,hf,ev⟩ := h
  exact ⟨f,sub f hf,ev⟩

private theorem grow (c : Scope H k) (U V p hp)
    (pure : ∀ f∈c.q.pure, f∈p.pure) (pool : ∀ f∈c.q.pool, f∈p.pool) :
    Extends xs c (enlarge c U V p hp) where
  low := fun h => h.imp_right (fun given => hasMono (given.extend _) pure)
  high := fun h => hasMono (h.extend _) pool

private theorem inputs (c : Scope H k) (U V : Sources) :
    let bank := c.bank++[representative H U,representative H V]
    (Low c xs U → Has (signal xs) bank (choices c.q (2*k)) (signal xs U)) ∧
    (Low c xs V → Has (signal xs) bank (choices c.q (2*k+1)) (signal xs V)) := by
  constructor
  · rintro (yes|old)
    · refine ⟨_,List.mem_cons_self ..,?_⟩
      rw [←c.size]
      simpa [representative,yes] using
        leftAtom (signal xs) c.bank (representative H U) (representative H V)
    · exact hasMono (old.extend _) (fun _ => List.mem_cons_of_mem _)
  · rintro (yes|old)
    · refine ⟨_,List.mem_cons_self ..,?_⟩
      rw [←c.size]
      simpa [representative,yes] using
        rightAtom (signal xs) c.bank (representative H U) (representative H V)
    · exact hasMono (old.extend _) (fun _ => List.mem_cons_of_mem _)

theorem highZero (c : Scope H k) : High c xs ∅ :=
  ⟨[],(poolFacts (X:=X) c.reachable).1,fun _ => evalEmpty _⟩
theorem highJoin (c : Scope H k) {v w} (a : High c xs v) (b : High c xs w) : High c xs (v∪w) :=
  a.join (poolFacts c.reachable).2 b

private theorem inserted {read : Sources → Set X} {bank : List Sources} (c : Scope H k) (f n) {v}
    (real : Real read bank f v) : Has read bank (supply c.q f n).pool v := by
  refine ⟨either f [],List.mem_append_right _ (List.mem_map.mpr ⟨[],(poolFacts (X:=X) c.reachable).1,rfl⟩),?_⟩
  intro tail
  rw [evalEither,real tail,evalEmpty,Set.union_empty]

private theorem supplied (c : Scope H k) (U V f n) (hp : supply c.q f n∈next k c.q) {v : Set X}
    (real : Real (signal xs) (c.bank++[representative H U,representative H V]) f v) :
    ∃ d : Scope H (k+1), d.q.cut=(c.q.cut || n) ∧ Extends xs c d ∧ High d xs v :=
  ⟨enlarge c U V _ hp,rfl,grow c U V _ hp (fun _ h => h) (fun _ h => List.mem_append_left _ h),inserted c f n real⟩

theorem lowUnion (c : Scope H k) {U V} (a : Low c xs U) (b : Low c xs V) :
    ∃ d : Scope H (k+1), d.q.cut=c.q.cut ∧ Extends xs c d ∧ Low d xs (U∪V) := by
  obtain ⟨f,hf,ef⟩ := (inputs c U V).1 a
  obtain ⟨g,hg,eg⟩ := (inputs c U V).2 b
  let p := store c.q (either f g)
  have hp : p∈next k c.q := by
    simp only [next,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨f,hf,g,hg,rfl⟩))
  refine ⟨enlarge c U V p hp,rfl,grow c U V _ hp (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h),
    Or.inr ⟨either f g,List.mem_cons_self ..,?_⟩⟩
  rw [signalUnion]; exact ef.join eg

theorem highProduct (c : Scope H k) {U V} (a : Low c xs U) (b : Low c xs V) :
    ∃ d : Scope H (k+1), d.q.cut=c.q.cut ∧ Extends xs c d ∧ High d xs (signal xs U ∩ signal xs V) := by
  obtain ⟨f,hf,ef⟩ := (inputs c U V).1 a
  obtain ⟨g,hg,eg⟩ := (inputs c U V).2 b
  have hp : supply c.q (both f g) false∈next k c.q := by
    simp only [next,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inl (Or.inl (Or.inr ⟨f,hf,g,hg,rfl⟩))
  simpa using supplied c U V (both f g) false hp (ef.meet eg)

theorem highMixed (c : Scope H k) {U v} (a : Low c xs U) (b : High c xs v) :
    ∃ d : Scope H (k+1), d.q.cut=c.q.cut ∧ Extends xs c d ∧ High d xs (signal xs U ∪ v) := by
  obtain ⟨f,hf,ef⟩ := (inputs c U ∅).1 a
  have hp : supply c.q f false∈next k c.q := by
    simp only [next,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inl (Or.inr ⟨f,hf,rfl⟩)
  obtain ⟨d,cut,ext,ha⟩ := supplied c U ∅ f false hp ef
  exact ⟨d,by simpa using cut,ext,highJoin d ha (ext.high b)⟩

theorem highNestedLow (c : Scope H k) {v U} (a : High c xs v) (b : Low c xs U) :
    ∃ d : Scope H (k+1), d.q.cut=true ∧ Extends xs c d ∧ High d xs (v∩signal xs U) := by
  obtain ⟨f,hf,ef⟩ := a
  obtain ⟨g,hg,eg⟩ := (inputs c U ∅).1 b
  have hp : supply c.q (both f g) true∈next k c.q := by
    simp only [next,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inr ⟨f,hf,g,Or.inl hg,rfl⟩
  obtain ⟨d,cut,ext,h⟩ := supplied c U ∅ _ true hp ((ef.extend _).meet eg)
  exact ⟨d,by simpa using cut,ext,h⟩

theorem highNested (c : Scope H k) {v w} (a : High c xs v) (b : High c xs w) :
    ∃ d : Scope H (k+1), d.q.cut=true ∧ Extends xs c d ∧ High d xs (v∩w) := by
  obtain ⟨f,hf,ef⟩ := a
  obtain ⟨g,hg,eg⟩ := b
  have hp : supply c.q (both f g) true∈next k c.q := by
    simp only [next,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inr ⟨f,hf,g,Or.inr hg,rfl⟩
  obtain ⟨d,cut,ext,h⟩ := supplied c ∅ ∅ _ true hp ((ef.meet eg).extend _)
  exact ⟨d,by simpa using cut,ext,h⟩

#print axioms lowUnion
#print axioms highNested
end Checkpoint124.Library
