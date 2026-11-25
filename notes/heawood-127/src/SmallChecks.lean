import SmallData
import ReadOnce

namespace Checkpoint127.Small
open Checkpoint125
abbrev Row := Fin 128
abbrev Slot (k : Bool) := {s : ℕ // s∈palette k}

def signal (s : ℕ) (r : Row) := (s &&& r.val)!=0
def target (k : Bool) (r : Row) := (positives k).any (fun e => e &&& r.val == e)
def gate (c : Case) (r : Row) :=
  if c.isOr then signal c.x r || signal c.y r else signal c.x r && signal c.y r
def seen (c : Case) (t : Option ℕ) (r : Row) := t.elim (gate c r) (fun n => signal n r)
def rowAt (c : Case) (h : Bool) (i : Fin 4) := c.rows.getD ((if h then 4 else 0)+i.val) 0
def column (c : Case) (t : Option ℕ) (h : Bool) := ((List.finRange 4).filter
  (fun i => seen c t (rowAt c h i))).foldr (fun i n => 2^i.val ||| n) 0
def signature (c : Case) (t : Option ℕ) := (column c t false,column c t true)
def terminals (k : Bool) : List (Option ℕ) := none::(palette k).map some

def Separates (k : Bool) (c : Case) (p : ℕ × Row × Row) : Prop :=
  p.1∈palette k ∧ target k p.2.1=true ∧ target k p.2.2=false ∧
  (gate c p.2.1=true → gate c p.2.2=true) ∧
  (∀ v∈palette k,v≠p.1 → signal v p.2.1=true → signal v p.2.2=true)
instance (k c p) : Decidable (Separates k c p) := by unfold Separates; infer_instance

def Switch (k : Bool) (c : Case) : Prop :=
  c.first∈palette k ∧ c.second∈palette k ∧
  (∀ t∈terminals k, signature c t∈Binary.catalog (decide (some c.first=t)) (decide (some c.second=t)) ∧
    ∀ (h : Bool) (i : Fin 4), Binary.bit (signature c t) h i=seen c t (rowAt c h i)) ∧
  ∀ (h : Bool) (i : Fin 4), target k (rowAt c h i)=Binary.bit (8,14) h i
instance (k c) : Decidable (Switch k c) := by unfold Switch; infer_instance

def Good (k : Bool) (c : Case) : Prop :=
  (c.needed.map Prod.fst).Nodup ∧ 6≤c.needed.length ∧
  (∀ p∈c.needed, Separates k c p) ∧ (7≤c.needed.length ∨ Switch k c)
instance (k c) : Decidable (Good k c) := by unfold Good; infer_instance

def table (k : Bool) := if k then clawCases else cycleCases
def Match (c : Case) (x y : ℕ) (op : Bool) := c.isOr=op ∧ (c.x=x ∧ c.y=y ∨ c.x=y ∧ c.y=x)
instance (c x y op) : Decidable (Match c x y op) := by unfold Match; infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem checked : ∀ k : Bool,
    (∀ s∈palette k, ∃ r : Row, signal s r≠target k r) ∧
    (∀ x∈palette k, ∀ y∈palette k, ∀ op : Bool, x≠y → ∃ c∈table k, Match c x y op) ∧
    (∀ c∈table k, Good k c) := by decide +kernel

#print axioms checked
end Checkpoint127.Small
