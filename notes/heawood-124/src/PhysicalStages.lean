import StageSupport

namespace PEqualNP.Outside.L_meta_2268_aux.Normal.Stage

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity StarUnion Finset

/-- A project circuit with arbitrary binary OR preprocessing, binary products of
preprocessed wires, and binary OR postprocessing. The postprocessing indices refer
locally to all middle outputs followed by the previous postprocessing wires. -/
def circuit (n : ℕ) (bot mid top : List Port) (out : ℕ) : Circuit :=
  ⟨bot.map (gate GateOp.or 0) ++ mid.map (gate GateOp.and 0) ++
      top.map (gate GateOp.or (n+bot.length)),
    n+bot.length+out⟩

theorem physicalSize (n) (bot mid top : List Port) (out) :
    (circuit n bot mid top out).size = bot.length + mid.length + top.length := by
  simp [circuit,Circuit.size,Nat.add_assoc]

theorem physicalFanInTwo (n) (bot mid top : List Port) (out) :
    FanInTwo (circuit n bot mid top out) := by
  intro g hg
  simp only [circuit,List.mem_append,List.mem_map] at hg
  rcases hg with (⟨p,_,rfl⟩ | ⟨p,_,rfl⟩) | ⟨p,_,rfl⟩ <;> simp [gate]

private theorem sourceLength (n) (l : List Port) : (sourceWires n l).length = n+l.length := by
  simp [sourceWires,bases,supportLength]
private theorem schedLength (n) (l : List Port) : (sched n l).length = l.length := by
  simp [sched,supportLength]

private theorem orEval (l : List Port) {k : ℕ} (v : Fin k → Bool) (pre : List Bool) :
    Build.wiresFrom (l.map (gate GateOp.or pre.length)) (pre ++ List.ofFn v) =
      pre ++ (sourceWires k l).map (reads v) := by
  have b : (bases k).map (reads v) = List.ofFn v := by
    simp [bases, List.map_ofFn, Function.comp_def]
  have h := orTransport l (bases k) v pre
  rw [b] at h
  exact h

private def valAnd (w : List Bool) (p : Port) : Bool := w.getD p.1 false && w.getD p.2 false

private theorem midEval (l : List Port) (w extra : List Bool)
    (valid : ∀ p ∈ l, p.1 < w.length ∧ p.2 < w.length) :
    Build.wiresFrom (l.map (gate GateOp.and 0)) (w ++ extra) = w ++ (extra ++ l.map (valAnd w)) := by
  induction l generalizing extra with
  | nil => simp [Build.wiresFrom]
  | cons p l ih =>
    obtain ⟨a,b⟩ := p
    obtain ⟨ha,hb⟩ := valid (a,b) (List.mem_cons_self ..)
    have step : (gate GateOp.and 0 (a,b)).op.eval
        ((gate GateOp.and 0 (a,b)).inputs.map (fun i => (w++extra).getD i false))
        = valAnd w (a,b) := by
      simp only [gate,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,
        Bool.and_true,Nat.zero_add,List.getD_append _ _ _ _ ha,List.getD_append _ _ _ _ hb,valAnd]
    change Build.wiresFrom (l.map (gate GateOp.and 0)) ((w ++ extra) ++ [_]) = _
    rw [step,List.append_assoc,ih _ (fun p h => valid p (List.mem_cons_of_mem _ h))]
    simp

private def leftSide (n : ℕ) (bot mid : List Port) (i : Fin mid.length) : Finset (Fin n) :=
  (sourceWires n bot).getD (mid[i].1) ∅
private def rightSide (n : ℕ) (bot mid : List Port) (i : Fin mid.length) : Finset (Fin n) :=
  (sourceWires n bot).getD (mid[i].2) ∅
private def active (mid top : List Port) (out : ℕ) : Finset (Fin mid.length) :=
  (sourceWires mid.length top).getD out ∅

/-- The reachable AND indices are extracted from the actual selected output. -/
theorem physicalTruth (n : ℕ) (bot mid top : List Port) (out : ℕ)
    (valid : ∀ p ∈ mid, p.1 < n+bot.length ∧ p.2 < n+bot.length) (z : Fin n → Bool) :
    circuitFun n (circuit n bot mid top out) z = true ↔
    reachableTruth (active mid top out) (leftSide n bot mid) (rightSide n bot mid) z := by
  let w := (sourceWires n bot).map (reads z)
  let vb (i : Fin mid.length) := reads z (leftSide n bot mid i) && reads z (rightSide n bot mid i)
  have wl : w.length = n+bot.length := by simp [w,sourceLength]
  have low : Build.wiresFrom (bot.map (gate GateOp.or 0)) (List.ofFn z) = w := by
    simpa [w] using orEval bot z []
  have well : ∀ p ∈ mid, p.1 < w.length ∧ p.2 < w.length := by simpa [wl] using valid
  have mids : mid.map (valAnd w) = List.ofFn vb := by
    rw [← List.ofFn_getElem_eq_map mid (valAnd w)]
    apply congrArg List.ofFn
    funext i
    simp only [valAnd,w,readsGet,vb,leftSide,rightSide,Fin.getElem_fin]
  have between : Build.wiresFrom (mid.map (gate GateOp.and 0)) w = w ++ List.ofFn vb := by
    simpa [mids] using midEval mid w [] well
  have high := orEval top vb w
  rw [wl] at high
  change (Build.wiresFrom _ _).getD _ false = true ↔ _
  rw [show (circuit n bot mid top out).gates =
    (bot.map (gate GateOp.or 0) ++ mid.map (gate GateOp.and 0)) ++
    top.map (gate GateOp.or (n + bot.length)) by rfl]
  rw [Build.wiresFrom_append,Build.wiresFrom_append,low,between,high]
  change (w ++ (sourceWires mid.length top).map (reads vb)).getD (n+bot.length+out) false = true ↔ _
  rw [List.getD_append_right _ _ _ _ (by omega),show n + bot.length + out - w.length = out by omega,
      readsGet,readsIff]
  change (∃ i ∈ active mid top out, vb i = true) ↔ _
  simp only [vb,Bool.and_eq_true,readsIff,reachableTruth]

/-- Actual Circuit.size lower bound for arbitrary physical fanout within both OR
stages and any number of redundant or unused gates. -/
theorem physicalLower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (reg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (iso : ∀ u v, G.Adj u v → u ∉ A)
    (girth : ∀ z (p : G.Walk z z), p.IsCycle → 5 ≤ p.length)
    (bot mid top : List Port) (out : ℕ)
    (valid : ∀ p ∈ mid, p.1 < n+bot.length ∧ p.2 < n+bot.length)
    (computes : ∀ z, circuitFun n (circuit n bot mid top out) z = true ↔
      ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) :
    2*(n-A.card) - 1 ≤ (circuit n bot mid top out).size := by
  have h := sharedORLower G A reg iso girth (sched n bot) (scheduled n bot).1
    (leftSide n bot mid) (rightSide n bot mid)
    (fun i => (scheduled n bot).2 (mid[i].1)) (fun i => (scheduled n bot).2 (mid[i].2))
    (sched mid.length top) (scheduled mid.length top).1
    (active mid top out) ((scheduled mid.length top).2 out)
    (fun z => (physicalTruth n bot mid top out valid z).symm.trans (computes z))
  simpa only [physicalSize,schedLength] using h

end PEqualNP.Outside.L_meta_2268_aux.Normal.Stage
