import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Abel

namespace Checkpoint135


abbrev Label (s p : ℕ) := Fin s × Fin p

def address {n s p : ℕ} (i : Fin n) (c : Fin s) (a : Fin p) : ℕ :=
  (i.val*s+c.val)*p+a.val

def guardTest {n s p : ℕ} [NeZero n] [NeZero p]
    (pattern : Fin n → Fin n → Fin p → Bool) (guard : Fin n → Fin s → Fin p → ℕ) (v : ℕ) : Bool :=
  let i := Fin.ofNat n v
  decide (∀ (c : Fin s) (a : Fin p) (j : Fin n) (d : Fin s) (b : Fin p),
    c≠d ∨ pattern i j (b-a)=true → (guard i c a).testBit (address j d b)=true)

/-- Keep the finite-index conversion abstract over the two data tables. -/
theorem checkedGuards {n s p : ℕ} [NeZero n] [NeZero p]
    (pattern : Fin n → Fin n → Fin p → Bool) (guard : Fin n → Fin s → Fin p → ℕ)
    (checked : ∀ k, k<n → guardTest pattern guard k=true)
    (i : Fin n) (c : Fin s) (a : Fin p) (j : Fin n) (d : Fin s) (b : Fin p) :
    c≠d ∨ pattern i j (b-a)=true → (guard i c a).testBit (address j d b)=true := by
  have h := checked i.val i.isLt
  unfold guardTest at h
  rw [Fin.ofNat_val_eq_self] at h
  exact of_decide_eq_true h c a j d b

structure Search (n s p : ℕ) [NeZero p] where
  pattern : Fin n → Fin n → Fin p → Bool
  guard : Fin n → Fin s → Fin p → ℕ
  correct : ∀ i c a j d b, c ≠ d ∨ pattern i j (b-a) = true →
    (guard i c a).testBit (address j d b) = true
  pivot : ℕ → Fin n
  child : ℕ → Fin s → Fin p → ℕ

namespace Search
variable {n s p : ℕ} [NeZero p] (D : Search n s p)

def compatible (f : Fin n → Label s p) : Prop :=
  ∀ i j, (f i).1 ≠ (f j).1 ∨ D.pattern i j ((f j).2-(f i).2) = true

def admits (w : ℕ) (f : Fin n → Label s p) : Prop :=
  ∀ i, w.testBit (address i (f i).1 (f i).2) = true

def free (w used : ℕ) : Prop := ∀ (i : Fin n) (c : Fin s) (a : Fin p),
  used ≤ c.val → w.testBit (address i c a) = true

def eligible (used : ℕ) (c : Fin s) (a : Fin p) : Bool :=
  decide (c.val < used ∨ c.val = used ∧ a = 0)

/-- A slot that has never been used can be renamed, and its first phase can be set to zero. -/
theorem normalize (w used : ℕ) (v : Fin n) (f : Fin n → Label s p)
    (good : D.compatible f) (fits : admits w f) (spare : free (n:=n) (s:=s) (p:=p) w used) :
    ∃ g, D.compatible g ∧ admits w g ∧ eligible used (g v).1 (g v).2 = true := by
  by_cases old : (f v).1.val < used
  · exact ⟨f,good,fits,decide_eq_true (Or.inl old)⟩
  have hu : used < s := by have := (f v).1.isLt; omega
  let next : Fin s := ⟨used,hu⟩
  let k := (f v).1
  let perm := Equiv.swap k next
  let g (i : Fin n) : Label s p :=
    (perm (f i).1,if (f i).1=k then (f i).2-(f v).2 else (f i).2)
  refine ⟨g,?_,?_,?_⟩
  · intro i j
    by_cases e : (f i).1=(f j).1
    · right
      have z := (good i j).resolve_left (not_not_intro e)
      change D.pattern i j ((if (f j).1=k then (f j).2-(f v).2 else (f j).2) -
        (if (f i).1=k then (f i).2-(f v).2 else (f i).2))=true
      rw [e]
      split
      · convert z using 2
        abel
      · exact z
    · exact Or.inl (fun h => e (perm.injective h))
  · intro i
    by_cases e : (f i).1=k
    · have z := spare i next ((g i).2) (le_refl _)
      simpa only [g,perm,e,Equiv.swap_apply_left] using z
    · by_cases h : (f i).1=next
      · have hk : used ≤ k.val := Nat.le_of_not_gt old
        have z := spare i k ((g i).2) hk
        simpa only [g,perm,h,Equiv.swap_apply_right] using z
      · simpa only [g,perm,Equiv.swap_apply_of_ne_of_ne e h,ite_eq_right e] using fits i
  · simp [eligible,g,k,perm,next]

/-- Each node records its domain and the number of slots already introduced. -/
structure Tree where
  domain : ℕ → ℕ
  used : ℕ → ℕ

def checkNode (T : Tree) (node : ℕ) : Bool :=
  let i := D.pivot node
  let w := T.domain node
  let used := T.used node
  decide (∀ (c : Fin s) (a : Fin p),eligible used c a=true →
    w.testBit (address i c a)=true →
    let child := D.child node c a
    child < node ∧ T.domain child=w &&& D.guard i c a ∧ T.used child=max used (c.val+1))

theorem sound (T : Tree) (count : ℕ) (ok : ∀ v, v<count → D.checkNode T v=true)
    (node : ℕ) (small : node<count) (spare : free (n:=n) (s:=s) (p:=p) (T.domain node) (T.used node))
    (f : Fin n → Label s p) (good : D.compatible f) (fits : admits (T.domain node) f) : False := by
  induction node using Nat.strong_induction_on generalizing f with
  | ind node ih =>
    let i := D.pivot node
    obtain ⟨g,cc,ww,choice⟩ := D.normalize _ _ i f good fits spare
    let c := (g i).1
    let a := (g i).2
    obtain ⟨earlier,domain,used⟩ := of_decide_eq_true (ok node small) c a choice (ww i)
    refine ih _ earlier (lt_trans earlier small) ?_ g cc ?_
    · rw [domain,used]
      intro j d b bound
      have hu : T.used node ≤ d.val := le_trans (le_max_left ..) bound
      have hc : c.val < d.val := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right ..) bound)
      exact (Nat.testBit_and ..).trans (Bool.and_eq_true_iff.mpr ⟨spare j d b hu,D.correct _ _ _ _ _ _ (Or.inl (Fin.ne_of_lt hc))⟩)
    · rw [domain]
      intro j
      exact (Nat.testBit_and ..).trans (Bool.and_eq_true_iff.mpr ⟨ww j,D.correct _ _ _ _ _ _ (cc i j)⟩)

end Search
end Checkpoint135
