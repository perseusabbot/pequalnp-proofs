import PrefixClasses

namespace Checkpoint123.Controls
open Checkpoint122.Posted Checkpoint122.Prefix
open PEqualNP.Outside.L_meta_3008_aux (nums)

def opening : Fin 5 → Fin 65 := ![1,8,9,10,20]

private def reroute (old port : ℕ) :=
  if port=old then 35 else if 35≤port then port+1 else port

/-- Insert an idempotent AND on one star product, before the final six collectors.
Passing true forces just that AND to zero using the evaluator's out-of-range wire. -/
def make (i : Fin 5) (c : Fin 7) (zero : Bool) : List ℕ :=
  let origin := codes (opening i) true true (control (opening i))
  let old := 28+c.val
  let selected := if zero then 63 else old
  origin.take 21 ++ [code selected selected false] ++ (origin.drop 21).map (fun q =>
     code (reroute old (q%64)) (reroute old (q/64%64)) (decide (4096≤q)))

/-- Gate indices with an AND on an input path, in reverse order. -/
def nestedSites (qs : List ℕ) : List ℕ :=
  (qs.foldl (fun (s : List Bool × List ℕ) q =>
    let depends := s.1.getD (q%64) false || s.1.getD (q/64%64) false
    let isAnd := decide (q<4096)
    (s.1++[isAnd || depends], if isAnd && depends then (s.1.length-14)::s.2 else s.2))
    (List.replicate 14 false,[])).2

/-- Thirty-five 28-gate circuits solve the official packed truth table. Cutting their
single nested AND removes exactly the three positive rows incident to the chosen center. -/
theorem controls :
    ∀ i : Fin 5, ∀ c : Fin 7,
      let origin := codes (opening i) true true (control (opening i))
      let qs := make i c false
      qs.take 2=origin.take 2 ∧ qs.length=28 ∧ nestedSites qs=[21] ∧ output qs=2097151 ∧
        output (make i c true)=2097151-(nums.getD (7+c.val) 0 &&& 2097151) := by
  set_option maxRecDepth 18000 in
  set_option maxHeartbeats 5000000 in
  decide +kernel

#print axioms controls
end Checkpoint123.Controls
