import HeawoodStages

namespace Checkpoint123.Census
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Bit i denotes edge i in the project's Heawood edge list. -/
def spokeMask (v : ℕ) := edges.zipIdx.foldl (fun mask item =>
  if item.1.1=v ∨ item.1.2=v then mask ||| (1 <<< item.2) else mask) 0

/-- Fold the incident masks of the selected centers. -/
def coverMask (cs : List V) := cs.foldr (fun v m => spokeMask v.val ||| m) 0

def covered := ((List.finRange 14).sublistsLen 6).map coverMask
def indices (m : ℕ) := (List.finRange 21).filter (fun i => m.testBit i.val)
def complement (m : ℕ) := 2097151 ^^^ m

def omissions (m : ℕ) : List ℕ :=
  let hit := indices m
  if hit.length=17 then [complement m]
  else if hit.length=18 then hit.map (fun i => complement m ||| (1 <<< i.val))
  else []

def candidates := covered.flatMap omissions

theorem counts :
    covered.length=3003 ∧ (covered.countP (fun m => (indices m).length=17))=42 ∧
    (covered.countP (fun m => (indices m).length=18))=14 ∧ candidates.length=294 ∧
    candidates.Nodup ∧ candidates.all (fun m => decide (m<2097152 ∧ (indices m).length=4))=true := by
  set_option maxRecDepth 30000 in
  set_option maxHeartbeats 5500000 in
  decide +kernel

#print axioms counts
end Checkpoint123.Census
