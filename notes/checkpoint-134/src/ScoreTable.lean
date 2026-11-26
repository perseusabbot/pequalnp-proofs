import Projection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

namespace Checkpoint134
open Finset

abbrev Group := Fin 21
abbrev Offset := Fin 7
abbrev Pattern := Fin 128

def address (g : Group) (l : Offset) : Cell := finProdFinEquiv (g,l)
def pattern (mask : ℕ) (g : Group) : Pattern := ⟨(mask >>> (7*g.val))%128,Nat.mod_lt _ (by decide)⟩
def block (coin : Cell→ℕ) (g : Group) (p : Pattern) :=
  ∑ l : Offset, if p.val.testBit l.val then coin (address g l) else 0

def fast (table : Group → Pattern → ℕ) (mask : ℕ) := ∑ g : Group,table g (pattern mask g)

theorem fastCorrect {coin : Cell→ℕ} {table : Group→Pattern→ℕ}
    (exactTable : ∀ g p,table g p = block coin g p) (mask : ℕ) :
    fast table mask = tally coin mask := by
  unfold fast tally
  rw [←Equiv.sum_comp (finProdFinEquiv : Group × Offset ≃ Cell)]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro g _
  rw [exactTable,block]
  apply sum_congr rfl
  intro l _
  have bit : (pattern mask g).val.testBit l.val = mask.testBit (address g l).val := by
    change (((mask >>> (7*g.val)) % 2^7).testBit l.val) = mask.testBit (l.val+7*g.val)
    simp only [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,decide_eq_true l.isLt,Bool.true_and,Nat.add_comm l.val]
  simp only [bit,address]

end Checkpoint134
