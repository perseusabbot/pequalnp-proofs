import BinaryBudget

namespace Checkpoint125.Binary
abbrev Signature := ℕ × ℕ

/-- The four rows in each word run through the choices of two distinguished
variables. The two words correspond to two settings of all other inputs. -/
def bit (s : Signature) (h : Bool) (i : ℕ) := (if h then s.2 else s.1).testBit i
def combine : Bool → Signature → Signature → Signature
  | true, p, q => (p.1 ||| q.1,p.2 ||| q.2)
  | false, p, q => (p.1 &&& q.1,p.2 &&& q.2)

def signature {A} (ρ : A → Signature) : Tree A → Signature
  | .leaf v => ρ v
  | .gate op a b => combine op (signature ρ a) (signature ρ b)

theorem bitTruth {A} [DecidableEq A] (ρ : A → Signature) (e : Tree A) (h i) :
    bit (signature ρ e) h i=true ↔ e.eval (fun x => bit (ρ x) h i=true) := by
  induction e with
  | leaf => rfl
  | gate op a b ha hb =>
    cases op <;> cases h <;>
      simp only [signature,combine,bit,ite_true,Bool.false_eq_true,ite_false,Nat.testBit_or,Nat.testBit_and,
        Bool.and_eq_true_iff,Bool.or_eq_true_iff,Tree.eval] at ha hb ⊢ <;> tauto

private def values (x y : Bool) : List ℕ :=
  [0,15] ++ (if x then [10] else []) ++ (if y then [12] else []) ++ (if x && y then [8,14] else [])
def catalog (x y : Bool) : List Signature := (values x y).flatMap fun a =>
  ((values x y).filter fun b => !((a==8 && b==14) || (a==14 && b==8))).map (a,·)

private theorem closure : ∀ a b c d op : Bool, (a && c)=false → (b && d)=false →
    (catalog a b).all (fun p => (catalog c d).all (fun q =>
      decide (combine op p q∈catalog (a || c) (b || d))))=true := by decide +kernel

/-- A read-once expression cannot switch from the conjunction of two
distinguished inputs to their disjunction under a change of the other inputs. -/
theorem signatureBound {A : Type} [DecidableEq A] (x y : A) (ρ : A → Signature) (e : Tree A)
    (once : e.inputs.Nodup)
    (leaves : ∀ t∈e.inputs, ρ t∈catalog (decide (x=t)) (decide (y=t))) :
    signature ρ e ∈ catalog (decide (x∈e.inputs)) (decide (y∈e.inputs)) := by
  induction e with
  | leaf a => simpa [signature,Tree.inputs] using leaves a (List.mem_singleton_self _)
  | gate op l r il ir =>
    obtain ⟨ld,rd,apart⟩ := List.nodup_append'.mp once
    have left := il ld (fun t ht => leaves t (List.mem_append_left _ ht))
    have right := ir rd (fun t ht => leaves t (List.mem_append_right _ ht))
    have exclusive (t : A) : (decide (t∈l.inputs) && decide (t∈r.inputs))=false := by
      by_cases hl : t∈l.inputs
      · have hr : t∉r.inputs := fun hr => apart hl hr
        simp [hr]
      · simp [hl]
    have cl := closure _ _ _ _ op (exclusive x) (exclusive y)
    have mem := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cl _ left) _ right)
    have appendBit (t : A) : decide (t∈l.inputs++r.inputs)=(decide (t∈l.inputs) || decide (t∈r.inputs)) := by
      apply Bool.eq_iff_iff.mpr
      simp
    change combine op (signature ρ l) (signature ρ r) ∈
      catalog (decide (x∈l.inputs++r.inputs)) (decide (y∈l.inputs++r.inputs))
    rw [appendBit x,appendBit y]
    exact mem

def primitive (x y outer : Bool) : Signature :=
  if x then (10,10) else if y then (12,12) else if outer then (0,15) else (0,0)
theorem primitiveOK : ∀ x y outer : Bool, primitive x y outer∈catalog x y := by decide +kernel

theorem recover {p : Signature} {a b} (hp : p∈catalog a b)
    (rows : ∀ (h : Bool) (i : Fin 4), bit p h i = bit (8,14) h i) : False := by
  have checked : ∀ a b : Bool, (catalog a b).all (fun q =>
      decide (∃ h : Bool, ∃ i : Fin 4, bit q h i≠bit (8,14) h i))=true := by decide +kernel
  obtain ⟨h,i,ne⟩ := of_decide_eq_true (List.all_eq_true.mp (checked a b) p hp)
  exact ne (rows h i)

#print axioms signatureBound
end Checkpoint125.Binary
