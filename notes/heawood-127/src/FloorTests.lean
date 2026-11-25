import CycleAudit
import PatchData
import NineData
import TenData

namespace Checkpoint127.Numbers
open Checkpoint125.Certificate Checkpoint126.Certificate Checkpoint126.Heawood Checkpoint127.Heawood

def floorAt (m : ℕ) := [27,28,28,27,28,28,27,27,27,27,26,26,24,24,23,22,21,21,19,19,18,16].getD m 0
def high (m : ℕ) := if m=10 then 27 else floorAt m
def strong : List ℕ := (patches.filter (fun p => !p.claw)).map Patch.mask
def weak : List ℕ := (patches.filter Patch.claw).map Patch.mask++cores.map Prod.snd
def within (qs : List ℕ) (ew : ℕ) := qs.filter (fun q => q &&& ew == q)
def present (qs : List ℕ) (xw : ℕ) := qs.any (fun q => q &&& xw == 0)
def surcharge (ss ws : List ℕ) (xw v m : ℕ) :=
  if present ss xw then 3 else if present ws xw then 2 else if 3*v<4*m then 1 else 0

def packs := matchings++Checkpoint126.Nine.matchings
def outside (w : ℕ) (p : List (Fin 21)) := p.filter (fun i => !w.testBit i.val)
def meets (goal bound w v m bonus : ℕ) :=
  decide (goal+1≤21-m+bound+v+bonus) ||
    packs.any (fun es => decide (goal+1≤21-m+(outside w es).length+v+bonus))
def detailed (ew : ℕ) (ss ws : List ℕ) (v j m : ℕ) (xs : List (Fin 21)) :=
  let xw := word xs
  let w := ew ^^^ xw
  let b := surcharge ss ws xw v m
  meets (high m) j w v m b || (decide (m=10) && Ten.masks.contains w && meets 26 j w v m b)

def checkSet (d : ℕ) :=
  let es := interior d
  let ew := word es
  let v := (vertexList d).length
  let j := (retained d).length
  let ss := within strong ew
  let ws := within weak ew
  (List.range (es.length+1)).all fun m =>
    let bound := max j ((21-m+2)/3)
    decide (2*m<v) || decide (high m+1≤21-m+bound+v+(if 3*v<4*m then 1 else 0)) ||
      (es.sublistsLen (es.length-m)).all (detailed ew ss ws v bound m)

def segment (b : ℕ) := (List.range 64).all (fun i => checkSet (64*b+i))

end Checkpoint127.Numbers
