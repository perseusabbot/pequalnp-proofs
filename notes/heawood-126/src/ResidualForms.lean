import PrunedProgram

namespace Checkpoint124.Shapes
open Finset

abbrev Term := Finset ℕ
abbrev Form := List Term
def atom (i : ℕ) : Form := [{i}]

/-- Absorption keeps only inclusion-minimal conjunctions. -/
def addTerm (t : Term) (f : Form) : Form :=
  if f.any (fun u => decide (u⊆t)) then f else t :: f.filter (fun u => !decide (t⊆u))
def reduce (f : Form) : Form := f.foldr addTerm []
def either (f g : Form) := reduce (f++g)
def both (f g : Form) := reduce (f.flatMap (fun t => g.map (t∪·)))

structure Frame where
  pure : List Form
  pool : List Form
  cut : Bool

def start : Frame := ⟨[],[[]],false⟩
def store (q : Frame) (f : Form) := {q with pure := f::q.pure}
def supply (q : Frame) (f : Form) (nested : Bool) :=
  {q with pool := q.pool ++ q.pool.map (either f), cut := q.cut || nested}
def choices (q : Frame) (i : ℕ) := atom i :: q.pure

/-- Two fresh variables stand for arbitrary regular OR supports at each counted gate.
Joining any subset of already supplied signals is free in this relaxation. -/
def next (k : ℕ) (q : Frame) : List Frame :=
  let left := choices q (2*k)
  let right := choices q (2*k+1)
  (left.flatMap fun a => right.map (fun b => store q (either a b))) ++
  (left.flatMap fun a => right.map (fun b => supply q (both a b) false)) ++
  (left.map fun a => supply q a false) ++
  (q.pool.flatMap fun a => (left++q.pool).map (fun b => supply q (both a b) true))

def frames : ℕ → List Frame
  | 0 => [start]
  | k+1 => (frames k).flatMap (next k)

def cap : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | _ => 4

end Checkpoint124.Shapes
