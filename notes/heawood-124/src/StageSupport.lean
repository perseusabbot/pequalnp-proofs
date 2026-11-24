import SharedOR
import CoverBuild

namespace PEqualNP.Outside.L_meta_2268_aux.Normal.Stage

open StarUnion Finset PEqualNP.CircuitLowerBounds

abbrev Port := ℕ × ℕ

/-- Appended wire supports of a binary OR schedule, in chronological order. -/
def supportGates {V : Type} [DecidableEq V] (w : List (Finset V)) : List Port → List (Finset V)
  | [] => []
  | (a,b)::l =>
    let new := w.getD a ∅ ∪ w.getD b ∅
    new :: supportGates (w ++ [new]) l

theorem supportLength {V : Type} [DecidableEq V] (l : List Port) (w : List (Finset V)) :
    (supportGates w l).length = l.length := by
  induction l generalizing w with
  | nil => rfl
  | cons p l ih => simpa only [supportGates, List.length_cons] using congrArg Nat.succ (ih _)

theorem getReady {V : Type} [DecidableEq V] {w g : List (Finset V)}
    (h : ∀ s ∈ w, Ready g s) (i : ℕ) : Ready g (w.getD i ∅) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inl (by simp)

private theorem readyCons {V : Type} [DecidableEq V] {w : List (Finset V)} {s t : Finset V}
    (h : Ready w s) : Ready (t :: w) s := h.elim Or.inl (fun p => Or.inr (List.mem_cons_of_mem _ p))

theorem supportSchedule {V : Type} [DecidableEq V] (l : List Port) (w old : List (Finset V))
    (bok : Built old) (read : ∀ s ∈ w, Ready old s) :
    Built ((supportGates w l).reverse ++ old) ∧
    ∀ s ∈ w ++ supportGates w l, Ready ((supportGates w l).reverse ++ old) s := by
  induction l generalizing w old with
  | nil => simpa [supportGates] using And.intro bok read
  | cons p l ih =>
    rcases p with ⟨a,b⟩
    let new := w.getD a ∅ ∪ w.getD b ∅
    have bok' : Built (new :: old) := ⟨bok,_,_,rfl,getReady read a,getReady read b⟩
    have read' : ∀ s ∈ w ++ [new], Ready (new :: old) s := by
      intro s mem
      rcases List.mem_append.mp mem with left | right
      · exact readyCons (read s left)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp right)))
    simpa [supportGates,new,List.append_assoc] using ih (w++[new]) (new::old) bok' read'

def bases (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i => {i}
def sourceWires (n : ℕ) (l : List Port) := bases n ++ supportGates (bases n) l
def sched (n : ℕ) (l : List Port) := (supportGates (bases n) l).reverse

theorem readyBases (n : ℕ) (s : Finset (Fin n)) (h : s ∈ bases n) : Ready [] s := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  exact Or.inl (by simp)
theorem scheduled (n : ℕ) (l : List Port) : Built (sched n l) ∧
    ∀ i, Ready (sched n l) ((sourceWires n l).getD i ∅) := by
  have h := supportSchedule l (bases n) [] (by trivial) (readyBases n)
  simp only [List.append_nil] at h
  exact ⟨h.1, getReady h.2⟩

def reads {V : Type} (z : V → Bool) (s : Finset V) : Bool := decide (∃ v ∈ s, z v = true)

@[simp] theorem readsEmpty {V : Type} (z : V → Bool) : reads z ∅ = false := by simp [reads]
@[simp] theorem readsSingle {V : Type} (z : V → Bool) (v : V) : reads z {v} = z v := by simp [reads]
theorem readsIff {V : Type} (z : V → Bool) (s : Finset V) :
    reads z s = true ↔ ∃ v ∈ s, z v = true := by simp [reads]
theorem readsUnion {V : Type} [DecidableEq V] (z : V → Bool) (a b : Finset V) :
    reads z (a ∪ b) = (reads z a || reads z b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [readsIff,Bool.or_eq_true,Finset.mem_union]
  constructor
  · rintro ⟨i,hi,val⟩; rcases hi with left | right
    · exact Or.inl ⟨i,left,val⟩
    · exact Or.inr ⟨i,right,val⟩
  · rintro (⟨i,hi,val⟩ | ⟨i,hi,val⟩)
    · exact ⟨i,Or.inl hi,val⟩
    · exact ⟨i,Or.inr hi,val⟩

theorem readsGet {V : Type} (z : V → Bool) (w : List (Finset V)) (i : ℕ) :
    (w.map (reads z)).getD i false = reads z (w.getD i ∅) := by
  simpa using (List.getD_map (l := w) (d := ∅) (n := i) (reads z))

def gate (op : GateOp) (offset : ℕ) (p : Port) : Gate := ⟨op,[offset+p.1,offset+p.2]⟩

private theorem afterPrefix (p w : List Bool) (i : ℕ) :
    (p ++ w).getD (p.length+i) false = w.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem orTransport {V : Type} [DecidableEq V] (l : List Port) (w : List (Finset V))
    (z : V → Bool) (pref : List Bool) :
    Build.wiresFrom (l.map (gate GateOp.or pref.length)) (pref ++ w.map (reads z)) =
      pref ++ (w ++ supportGates w l).map (reads z) := by
  induction l generalizing w with
  | nil => simp [Build.wiresFrom,supportGates]
  | cons p l ih =>
    rcases p with ⟨a,b⟩
    let new := w.getD a ∅ ∪ w.getD b ∅
    have step : (gate GateOp.or pref.length (a,b)).op.eval
          ((gate GateOp.or pref.length (a,b)).inputs.map
            (fun i => (pref ++ w.map (reads z)).getD i false)) = reads z new := by
      simp only [gate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, afterPrefix, readsGet, new, readsUnion]
    change Build.wiresFrom (l.map (gate GateOp.or pref.length))
        ((pref ++ w.map (reads z)) ++ [_]) = _
    rw [step]
    simpa [supportGates,new,List.append_assoc] using ih (w ++ [new])

end PEqualNP.Outside.L_meta_2268_aux.Normal.Stage
