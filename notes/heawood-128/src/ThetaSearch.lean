import CherryBound

namespace Checkpoint128.Theta
open Finset Checkpoint125 Checkpoint126.Cherry

/-- Each bit position names a positive/negative row pair. The low half
records evaluations on its positive row and the high half on its negative row. -/
def width : ℕ := 110
def full : ℕ := 2^width-1
def distinction (x : ℕ) := full &&& x &&& (full ^^^ (x >>> width))
def mix (op : Bool) (x y : ℕ) := if op then x ||| y else x &&& y

def coveredBy (xs : List ℕ) := xs.foldr (fun x d => distinction x ||| d) 0

def picks {A : Type} : List A → List (A × List A)
  | [] => []
  | x::xs => (x,xs)::(picks xs).map (fun (y,r) => (y,x::r))

def pairs {A : Type} : List A → List (A × A × List A)
  | [] => []
  | x::xs => (picks xs).map (fun (y,r) => (x,y,r)) ++
      (pairs xs).map (fun (a,b,r) => (a,b,x::r))

/-- Explore the four possible last-use patterns for the operands of a gate.
The fresh output label is always live after cutting this gate. -/
def follow (k : ℕ) (go : List ℕ → Bool) (x y : ℕ) (r : List ℕ) (z : ℕ) : Bool :=
  let c := distinction z ||| coveredBy r
  let a := distinction x
  let b := distinction y
  let n := r.length+1
  (n≤k && c==full && go (z::r)) ||
  (n+1≤k && (c ||| a)==full && go (z::x::r)) ||
  (n+1≤k && (c ||| b)==full && go (z::y::r)) ||
  (n+2≤k && (c ||| a ||| b)==full && go (z::x::y::r))

def advance (k : ℕ) (go : List ℕ → Bool) (s : List ℕ) : Bool :=
  (pairs s).any fun (x,y,r) =>
    follow k go x y r (x &&& y) || follow k go x y r (x ||| y)

def search : ℕ → List ℕ → Bool
  | 0,s => s.any (fun x => distinction x==full)
  | k+1,s => s.any (fun x => distinction x==full) || advance (k+1) (search k) s

end Checkpoint128.Theta
