import ResidualLibrary

namespace Checkpoint124.Library
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint124.Shapes
open PEqualNP.Outside.L_meta_3004_aux.Controls

variable {X : Type}
def value (xs : X → (V → Bool)) (w : Wire 14) : Set X := {z | w.full (xs z)=true}
def events (H : Graph) (J : Finset (Product 14)) (s : State 14) := waste H s.bottom+extra J s+s.dropped

private theorem pureValue {xs : X → (V → Bool)} {B T P d x} {w : Wire 14}
    (f : Fits B T P d x w) (hp : w.pure=true) : value xs w=signal xs w.raw := by
  ext z
  have eq : accepts w (xs z) ↔ lit w.raw (xs z) := by simp [accepts,Wire.jobs,f.empty hp]
  exact ⟨fun h => eq.mp (f.same (by simp [f.empty hp]) _ h),fun h => f.sound _ (eq.mpr h)⟩

private theorem valueJoin (xs : X → (V → Bool)) (a b : Wire 14) :
    value xs (joinW a b)=value xs a ∪ value xs b := by ext z; simp [value,joinW]
private theorem valueMeet (xs : X → (V → Bool)) (a b : Wire 14) :
    value xs (meetW a b)=value xs a ∩ value xs b := by ext z; simp [value,meetW]
private theorem valueCut (xs : X → (V → Bool)) (a b : Wire 14) :
    value xs (cutW a b)=value xs a ∩ value xs b := by ext z; simp [value,cutW]

private structure Tracked {H k} (c : Scope H k) (xs : X → (V → Bool))
    (B : List Sources) (W : List (Wire 14)) : Prop where
  bottom : ∀ U∈B, Low c xs U
  wires : ∀ w∈W, w.pure=false → High c xs (value xs w)

private theorem Tracked.move {H k l} {xs : X → (V → Bool)} {c : Scope H k} {d : Scope H l} {B W}
    (h : Tracked c xs B W) (e : Extends xs c d) : Tracked d xs B W :=
  ⟨fun U hu => e.low (h.bottom U hu),fun w hw hp => e.high (h.wires w hw hp)⟩

private theorem Tracked.push {H k} {xs : X → (V → Bool)} {c : Scope H k} {B W} (h : Tracked c xs B W)
    (w : Wire 14) (fresh : w.pure=false → High c xs (value xs w)) : Tracked c xs B (W++[w]) := by
  refine ⟨h.bottom,?_⟩
  intro u hu hp
  rcases List.mem_append.mp hu with old|last
  · exact h.wires _ old hp
  · obtain rfl := List.mem_singleton.mp last
    exact fresh hp

private theorem Tracked.store {H k} {xs : X → (V → Bool)} {c : Scope H k} {B W} (h : Tracked c xs B W)
    (U) (fresh : Low c xs U) : Tracked c xs (U::B) W :=
  ⟨fun _ hu => (List.mem_cons.mp hu).elim (fun eq => eq ▸ fresh) (h.bottom _),h.wires⟩

private theorem Tracked.atPort {H k} {xs : X → (V → Bool)} {c : Scope H k} {B W}
    (h : Tracked c xs B W) (i : ℕ) (hp : (W.getD i default).pure=false) :
    High c xs (value xs (W.getD i default)) := by
  by_cases hi : i<W.length
  · rw [List.getD_eq_getElem _ _ hi] at hp ⊢
    exact h.wires _ (List.getElem_mem ..) hp
  · rw [List.getD_eq_default _ _ (by omega)] at hp
    contradiction

private def Modeled (H : Graph) (J : Finset (Product 14)) (xs : X → (V → Bool)) (s : State 14) :=
  ∃ c : Scope H (events H J s), (c.q.cut=true ↔ 0<s.dropped) ∧ Tracked c xs s.bottom s.wires

private theorem finish {H J} {xs : X → (V → Bool)} {t : State 14} {k} (c : Scope H k)
    (cost : events H J t=k) (cut : c.q.cut=true ↔ 0<t.dropped) (tracked : Tracked c xs t.bottom t.wires) :
    Modeled H J xs t := by unfold Modeled; rw [cost]; exact ⟨c,cut,tracked⟩

private theorem stepModel {H J} {xs : X → (V → Bool)} {s} (v : Valid s) (g : Op)
    (dead : ∀ p∈J, signal xs p.1 ∩ signal xs p.2=∅) (before : Modeled H J xs s) :
    Modeled H J xs (step s g) := by
  obtain ⟨c,prior,old⟩ := before
  let a := s.wires.getD g.left default
  let b := s.wires.getD g.right default
  have fa := port v g.left
  have fb := port v g.right
  have low {w} (f : Fits s.bottom s.top s.products s.dropped s.bypass w)
      (hp : w.pure=true) : Low c xs w.raw := by
    rcases f.low hp with small|prev
    · exact Or.inl (Or.inl small)
    · exact old.bottom _ prev
  have atA (hp : a.pure=false) := old.atPort g.left hp
  have atB (hp : b.pure=false) := old.atPort g.right hp
  change Modeled H J xs (act s a b g.isOr)
  cases bothPure : a.pure && b.pure with
  | true =>
    obtain ⟨ap,bp⟩ := Bool.and_eq_true_iff.mp bothPure
    have ea := pureValue (xs:=xs) fa ap
    have eb := pureValue (xs:=xs) fb bp
    cases g.isOr with
    | true =>
      simp only [act,bothPure]
      by_cases ok : Regular H (a.raw∪b.raw)
      · refine finish c ?_ ?_ ?_
        · simp [events,waste,extra,ok]
        · exact prior
        · exact (old.store _ (Or.inl ok)).push (joinW a b) (by simp [joinW,bothPure])
      · obtain ⟨d,cut,ex,fresh⟩ := lowUnion c (low fa ap) (low fb bp)
        refine finish d ?_ ?_ ?_
        · simp [events,waste,extra,ok]; omega
        · rw [cut]; exact prior
        · exact ((old.move ex).store _ fresh).push (joinW a b) (by simp [joinW,bothPure])
    | false =>
      simp only [act,bothPure]
      by_cases live : (a.raw,b.raw)∈J
      · refine finish c ?_ ?_ ?_
        · simp [events,waste,extra,live]
        · exact prior
        · refine old.push (meetW a b) (fun _ => ?_)
          rw [valueMeet,ea,eb,dead _ live]
          exact highZero c
      · obtain ⟨d,cut,ex,fresh⟩ := highProduct c (low fa ap) (low fb bp)
        refine finish d ?_ ?_ ?_
        · simp [events,waste,extra,live]; omega
        · rw [cut]; exact prior
        · refine (old.move ex).push (meetW a b) (fun _ => ?_)
          rwa [valueMeet,ea,eb]
  | false =>
    cases mixed : a.pure || b.pure with
    | false =>
      obtain ⟨ap,bp⟩ := Bool.or_eq_false_iff.mp mixed
      cases g.isOr with
      | true =>
        simp only [act,bothPure,mixed,Bool.false_eq_true,ite_false]
        refine finish c ?_ ?_ ?_
        · rfl
        · exact prior
        · refine old.push (joinW a b) (fun _ => ?_)
          rw [valueJoin]; exact highJoin c (atA ap) (atB bp)
      | false =>
        simp only [act,bothPure]
        obtain ⟨d,cut,ex,fresh⟩ := highNested c (atA ap) (atB bp)
        refine finish d rfl (by simp [cut]) ?_
        refine (old.move ex).push (cutW a b) (fun _ => ?_)
        rwa [valueCut]
    | true =>
      have eitherPure : (a.pure=true ∧ b.pure=false) ∨ (a.pure=false ∧ b.pure=true) := by
        cases ap : a.pure <;> cases bp : b.pure <;> simp_all
      cases g.isOr with
      | true =>
        simp only [act,bothPure,mixed,ite_true]
        have create : ∃ d : Scope H (events H J s+1),
            d.q.cut=c.q.cut ∧ Extends xs c d ∧ High d xs (value xs (joinW a b)) := by
          rw [valueJoin]
          rcases eitherPure with ⟨ap,bp⟩|⟨ap,bp⟩
          · rw [pureValue fa ap]; exact highMixed c (low fa ap) (atB bp)
          · rw [pureValue fb bp,Set.union_comm]; exact highMixed c (low fb bp) (atA ap)
        obtain ⟨d,cut,ex,fresh⟩ := create
        refine finish d ?_ ?_ ?_
        · simp [events,extra]; omega
        · rw [cut]; exact prior
        · exact (old.move ex).push _ (fun _ => fresh)
      | false =>
        simp only [act,bothPure]
        have create : ∃ d : Scope H (events H J s+1),
            d.q.cut=true ∧ Extends xs c d ∧ High d xs (value xs (cutW a b)) := by
          rw [valueCut]
          rcases eitherPure with ⟨ap,bp⟩|⟨ap,bp⟩
          · rw [pureValue fa ap,Set.inter_comm]; exact highNestedLow c (atB bp) (low fa ap)
          · rw [pureValue fb bp]; exact highNestedLow c (atA ap) (low fb bp)
        obtain ⟨d,cut,ex,fresh⟩ := create
        exact finish d rfl (by simp [cut]) ((old.move ex).push _ (fun _ => fresh))

/-- On a domain where the selected ordinary products vanish, every impure
output is represented by the finite gate model, uniformly on that domain. -/
theorem representation (H : Graph) (J : Finset (Product 14)) (xs : X → (V → Bool)) (gs : List Op)
    (dead : ∀ p∈J, signal xs p.1 ∩ signal xs p.2=∅) (out : ℕ)
    (imp : ((run 14 gs).wires.getD out default).pure=false) :
    let s := run 14 gs
    ∃ c : Scope H (events H J s), (c.q.cut=true ↔ 0<s.dropped) ∧
      High c xs (value xs (s.wires.getD out default)) := by
  have all (ops : List Op) : Modeled H J xs (run 14 ops) := by
    induction ops using List.reverseRecOn with
    | nil =>
      let c : Scope H 0 := ⟨start,List.mem_singleton_self _,[],rfl,by simp⟩
      refine finish c rfl (by change false=true ↔ 0<0; decide) ?_
      refine ⟨by simp [run,initial],?_⟩
      intro w hw hp
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      contradiction
    | append_singleton ops g ih =>
      simpa only [run,List.foldl_append,List.foldl_cons,List.foldl_nil] using stepModel (run_valid 14 ops).1 g dead ih
  obtain ⟨c,cut,h⟩ := all gs
  exact ⟨c,cut,h.atPort out imp⟩

#print axioms representation
end Checkpoint124.Library
