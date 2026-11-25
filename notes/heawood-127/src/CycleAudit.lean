import CycleData
import MatchingTable
import Mathlib.Data.List.Sublists

namespace Checkpoint126.Certificate
open Checkpoint125.Certificate Checkpoint126.Heawood

def floorAt (m : ℕ) := floor m + if 8≤m then 1 else 0

def word : List (Fin 21)→ℕ
  | [] => 0
  | i::is => 2^i.val ||| word is

theorem wordBit (is : List (Fin 21)) (i : Fin 21) : (word is).testBit i.val=true ↔ i∈is := by
  induction is with
  | nil => simp [word]
  | cons j js ih =>
    simp only [word,Nat.testBit_or,Bool.or_eq_true_iff,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    simp only [←Fin.ext_iff]
    tauto

def coresIn (es : List (Fin 21)) :=
  let available := word es
  cores.filter (fun q => q.2 &&& available == q.2)

def persists (coreList : List (ℕ×ℕ)) (xs : List (Fin 21)) :=
  let missing := word xs
  coreList.any (fun q => q.2 &&& missing == 0)

def checkSet (d : ℕ) :=
  let es := interior d
  let v := (vertexList d).length
  let j := (retained d).length
  let coreList := coresIn es
  (List.range (es.length+1)).all fun m =>
    let base := 21-m+max ((21-m+2)/3) j+v
    decide (2*m<v) || decide (floorAt m+1 ≤ base+(if 3*v<4*m then 1 else 0)) ||
      (decide (floorAt m+1≤base+2) && decide (es.length-m≤2) &&
        (es.sublistsLen (es.length-m)).all (persists coreList))

def cycleBlock (b : ℕ) := (List.range 128).all (fun i => checkSet (128*b+i))

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem checked (b : ℕ) (bound : b<128) : cycleBlock b=true := by
  interval_cases b <;> decide +kernel

theorem bitsCorrect : cores.all (fun q => (List.finRange 21).all (fun i =>
    inside q.1 i == q.2.testBit i.val))=true := by decide +kernel

#print axioms checked
end Checkpoint126.Certificate
