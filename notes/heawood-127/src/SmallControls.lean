import SmallChecks

namespace Checkpoint127.Small
private def program : Bool→List (Bool × ℕ × ℕ)
  | false => [(true,1,5),(false,0,6),(true,1,3),(false,2,8),(true,3,5),(false,4,10),(true,7,9),(true,12,11)]
  | true => [(true,0,4),(false,1,7),(true,0,5),(false,2,9),(true,0,6),(false,3,11),(true,8,10),(true,13,12)]

private def stage (qs : List Bool) (g : Bool × ℕ × ℕ) :=
  let a := qs.getD g.2.1 false
  let b := qs.getD g.2.2 false
  qs++[if g.1 then a || b else a && b]

/-- Eight ordinary gates suffice in each model, even when only its singleton
inputs are provided to the circuit. All operand indices and rows are checked. -/
theorem eightGateControls : ∀ k : Bool, (program k).length=8 ∧
    (∀ p∈(program k).zipIdx,p.1.2.1<(if k then 7 else 6)+p.2 ∧ p.1.2.2<(if k then 7 else 6)+p.2) ∧
    ∀ r : Row, ((program k).foldl stage ((List.range (if k then 7 else 6)).map r.val.testBit)).getLast?=some (target k r) := by
  set_option maxRecDepth 10000 in
  decide +kernel

#print axioms eightGateControls
end Checkpoint127.Small
