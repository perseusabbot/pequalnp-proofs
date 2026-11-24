import PrunedProgram

namespace Checkpoint123.Restriction
open Finset StarUnion Checkpoint122.Pruning

variable {n : ℕ}
abbrev Input (n : ℕ) := Fin n → Bool
def Local (D : Support n) (x : Input n) : Prop := ∀ i, x i=true → i∈D
def Tracks (D A : Support n) (f : Input n → Bool) : Prop :=
  ∀ x y, Local D x → Local D y → (∀ i ∈ A, x i=y i) → f x=f y

private theorem enlarge {D A B : Support n} {f} (h : Tracks D A f) (sub : A ⊆ B) : Tracks D B f :=
  fun x y lx ly eq => h x y lx ly (fun i hi => eq i (sub hi))

private theorem pureTruth {B T P d b} {w : Wire n} (f : Fits B T P d b w) (hp : w.pure=true) (x) :
    w.full x=true ↔ lit w.raw x := by
  have eq : accepts w x ↔ lit w.raw x := by simp [accepts,Wire.jobs,f.empty hp]
  exact ⟨fun h => eq.mp (f.same (by simp [f.empty hp]) x h),fun h => f.sound x (eq.mpr h)⟩

private theorem pureTracks {D : Support n} {B T P d b} {w : Wire n}
    (f : Fits B T P d b w) (hp : w.pure=true) : Tracks D (w.raw ∩ D) w.full := by
  intro x y lx ly eq
  apply Bool.eq_iff_iff.mpr
  rw [pureTruth f hp,pureTruth f hp]
  constructor
  · rintro ⟨i,hi,yes⟩
    exact ⟨i,hi,(eq i (mem_inter.mpr ⟨hi,lx i yes⟩)).symm.trans yes⟩
  · rintro ⟨i,hi,yes⟩
    exact ⟨i,hi,(eq i (mem_inter.mpr ⟨hi,ly i yes⟩)).trans yes⟩

private def AllTracked (D A : Support n) (ws : List (Wire n)) : Prop :=
  ∀ w∈ws, w.pure=false → Tracks D A w.full

private theorem extend {D A A' : Support n} {ws : List (Wire n)} {w : Wire n}
    (tracked : AllTracked D A ws) (sub : A ⊆ A')
    (fresh : w.pure=false → Tracks D A' w.full) : AllTracked D A' (ws++[w]) := by
  intro u hu h
  rcases List.mem_append.mp hu with prev|last
  · exact enlarge (tracked u prev h) sub
  · obtain rfl := List.mem_singleton.mp last
    exact fresh h

private theorem atPort {D A : Support n} {ws : List (Wire n)} (h : AllTracked D A ws) (i : ℕ)
    (hp : (ws.getD i default).pure=false) : Tracks D A (ws.getD i default).full := by
  by_cases hi : i<ws.length
  · rw [List.getD_eq_getElem _ _ hi] at hp ⊢
    exact h _ (List.getElem_mem ..) hp
  · rw [List.getD_eq_default _ _ (by omega)] at hp
    contradiction

/-- An ordinary AND whose product vanishes on the restriction imports no variables. -/
def price (J : Finset (Product n)) (s : State n) :=
  2 * (s.products.filter (fun p => decide (p ∉ J))).length + s.bypass + s.dropped

private def Bound (D : Support n) (J : Finset (Product n)) (s : State n) : Prop :=
  ∃ A : Support n, A.card ≤ price J s ∧ AllTracked D A s.wires

private def imported (D : Support n) (w : Wire n) := if w.pure then w.raw ∩ D else ∅

private theorem stepBound {D : Support n} {J : Finset (Product n)} {s : State n} (valid : Valid s)
    (g : Op) (thin : ∀ U ∈ s.bottom, (U∩D).card≤1)
    (dead : ∀ p ∈ J, ∀ x, Local D x → ¬(lit p.1 x ∧ lit p.2 x))
    (h : Bound D J s) : Bound D J (step s g) := by
  obtain ⟨A,cap,tracked⟩ := h
  let a := s.wires.getD g.left default
  let b := s.wires.getD g.right default
  have fa := port valid g.left
  have fb := port valid g.right
  let N := A ∪ (imported D a ∪ imported D b)
  have small {w : Wire n} (fit : Fits s.bottom s.top s.products s.dropped s.bypass w) :
      (imported D w).card ≤ (if w.pure then 1 else 0) := by
    cases hp : w.pure with
    | false => simp [imported,hp]
    | true =>
      simp only [imported,hp,ite_true]
      rcases fit.low hp with lo|mem
      · exact (card_le_card inter_subset_left).trans lo
      · exact thin _ mem
  have na : imported D a ⊆ N := fun i hi => mem_union_right _ (mem_union_left _ hi)
  have nb : imported D b ⊆ N := fun i hi => mem_union_right _ (mem_union_right _ hi)
  have old : A ⊆ N := subset_union_left
  have feed (i) (sub : imported D (s.wires.getD i default) ⊆ N) :
      Tracks D N (s.wires.getD i default).full := by
    cases hp : (s.wires.getD i default).pure with
    | true => exact enlarge (pureTracks (port valid i) hp) (by simpa only [imported,hp,ite_true] using sub)
    | false => exact enlarge (atPort tracked i hp) old
  have ta := feed g.left na
  have tb := feed g.right nb
  have joint (op : Bool → Bool → Bool) : Tracks D N (fun x => op (a.full x) (b.full x)) := by
    intro x y lx ly eq
    exact congrArg₂ op (ta x y lx ly eq) (tb x y lx ly eq)
  have capN : N.card ≤ A.card + (if a.pure then 1 else 0) + (if b.pure then 1 else 0) := by
    have one := card_union_le A (imported D a ∪ imported D b)
    have two := card_union_le (imported D a) (imported D b)
    have ha := small fa
    have hb := small fb
    change (imported D a).card ≤ (if a.pure then 1 else 0) at ha
    change (imported D b).card ≤ (if b.pure then 1 else 0) at hb
    change (A ∪ (imported D a ∪ imported D b)).card ≤ _
    omega
  change Bound D J (act s a b g.isOr)
  unfold Bound
  by_cases pure : a.pure && b.pure
  · obtain ⟨ap,bp⟩ := Bool.and_eq_true_iff.mp pure
    cases op : g.isOr with
    | true =>
      simp only [act,pure]
      exact ⟨A,cap,extend tracked Subset.rfl (by simp [joinW,ap,bp])⟩
    | false =>
      simp only [act,pure]
      by_cases clean : (a.raw,b.raw) ∈ J
      · refine ⟨A,?_,extend tracked Subset.rfl (fun _ x y lx ly _ => ?_)⟩
        · simpa [price,List.filter_cons,clean] using cap
        · have off (z) (loc : Local D z) : (meetW a b).full z=false := by
            apply Bool.eq_false_iff.mpr
            intro on
            obtain ⟨aa,bb⟩ := Bool.and_eq_true_iff.mp on
            exact dead _ clean z loc ⟨(pureTruth fa ap z).mp aa,(pureTruth fb bp z).mp bb⟩
          exact (off x lx).trans (off y ly).symm
      · refine ⟨N,?_,extend tracked old (fun _ => joint Bool.and)⟩
        simp [price,clean] at cap ⊢
        simp [ap,bp] at capN
        omega
  · have cut : (a.pure && b.pure)=false := Bool.eq_false_iff.mpr pure
    cases op : g.isOr with
    | false =>
      simp only [act,cut]
      refine ⟨N,?_,extend tracked old (fun _ => joint Bool.and)⟩
      change N.card ≤ 2*(s.products.filter (fun p => decide (p ∉ J))).length+s.bypass+(s.dropped+1)
      unfold price at cap
      cases ap : a.pure <;> cases bp : b.pure <;> simp [ap,bp] at capN cut <;> omega
    | true =>
      by_cases anyPure : a.pure || b.pure
      · simp only [act,cut,anyPure,ite_true]
        refine ⟨N,?_,extend tracked old (fun _ => joint Bool.or)⟩
        change N.card ≤ 2*(s.products.filter (fun p => decide (p ∉ J))).length+(s.bypass+1)+s.dropped
        unfold price at cap
        cases ap : a.pure <;> cases bp : b.pure <;> simp [ap,bp] at capN cut <;> omega
      · have both := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr anyPure)
        simp only [act,cut,anyPure]
        refine ⟨N,?_,extend tracked old (fun _ => joint Bool.or)⟩
        exact (by simpa [both.1,both.2] using capN : N.card≤A.card) |>.trans cap

private theorem previousBottom (s : State n) (g : Op) : ∀ U∈s.bottom, U ∈ (step s g).bottom := by
  intro U hu
  unfold step act
  generalize (s.wires.getD g.left default) = a
  generalize (s.wires.getD g.right default) = b
  cases g.isOr <;> cases ap : a.pure <;> cases bp : b.pure <;> simp [hu]

/-- With at most one active terminal per pure wire, a nonvanishing ordinary AND imports
at most two terminals, a mixed OR or nested AND at most one, and other ORs import none. -/
theorem supportBudget (D : Support n) (J : Finset (Product n)) (gs : List Op)
    (thin : ∀ U ∈ (run n gs).bottom, (U∩D).card≤1)
    (dead : ∀ p ∈ J, ∀ x, Local D x → ¬(lit p.1 x ∧ lit p.2 x)) :
    ∃ A : Support n, A.card ≤ price J (run n gs) ∧
      ∀ i, ((run n gs).wires.getD i default).pure=false →
        Tracks D A ((run n gs).wires.getD i default).full := by
  suffices bound : Bound D J (run n gs) by
    obtain ⟨A,ha,h⟩ := bound
    exact ⟨A,ha,atPort h⟩
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨∅,by simp [price,run,initial],?_⟩
    intro w hw hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    contradiction
  | append_singleton gs g ih =>
    have eq : run n (gs++[g])=step (run n gs) g := by simp [run]
    rw [eq] at thin ⊢
    have prev := fun U (hU : U ∈ (run n gs).bottom) => thin U (previousBottom _ g _ hU)
    exact stepBound (run_valid n gs).1 g prev dead (ih prev)

#print axioms supportBudget
end Checkpoint123.Restriction
