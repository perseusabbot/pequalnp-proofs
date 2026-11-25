import MatchingData
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.FinRange

namespace Checkpoint125.Certificate

def vertexList (d : ℕ) := (List.finRange 14).filter fun v => d.testBit v.val
def pairAt (i : Fin 21) := pairs.getD i.val (0,0)
def inside (d : ℕ) (i : Fin 21) := d.testBit (pairAt i).1.val && d.testBit (pairAt i).2.val
def interior (d : ℕ) := (List.finRange 21).filter (inside d)
def choice (d : ℕ) := ((packed.getD (d/128) 0) >>> (5*(d%128))) % 32
def selected (d : ℕ) := matchings.getD (choice d) []
def retained (d : ℕ) := (selected d).filter fun i => !(inside d i)

/-- A lower bound on the number of gates at each of the 22 possible loss counts. -/
def floor (m : ℕ) := [27,28,28,27,28,28,27,27,26,25,24,24,22,22,21,20,19,19,17,17,16,14].getD m 0

def checkMask (d : ℕ) :=
  let v := (vertexList d).length
  let j := (retained d).length
  (List.range ((interior d).length+1)).all fun m => decide
    (v ≤ 2*m → floor m+1 ≤ 21-m + max ((21-m+2)/3) j + v + (if 3*v<4*m then 1 else 0))

def block (b : ℕ) := (List.range 128).all (fun i => checkMask (128*b+i))

end Checkpoint125.Certificate
