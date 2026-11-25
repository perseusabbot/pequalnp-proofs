import PrunedEdges
import PEqualNP.Outside.L_meta_3008

namespace Checkpoint122.Posted
open Checkpoint122.Pruning
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3004_aux.Controls
open PEqualNP.Outside.L_meta_3008_aux (nums)

def key (i : Fin 65) : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑i / (13 : ℕ)) []).getD (↑i % (13 : ℕ)) (0 : ℕ)

def code (a b : ℕ) (op : Bool) := a+64*b+if op=true then 4096 else 0

def codes (i : Fin 65) (f g : Bool) (tail : List (Fin 8192)) :=
  let k := key i
  code 0 (Fin.ofNat 14 (k/225)).val f ::
    code (Fin.ofNat 15 (k%225/15)).val (Fin.ofNat 15 (k%15)).val g :: tail.map Fin.val

def wordStep (xs : List ℕ) (q : ℕ) :=
  xs++[if q<4096 then xs.getD (q%64) 0 &&& xs.getD (q/64%64) 0
       else xs.getD (q%64) 0 ||| xs.getD (q/64%64) 0]

def output (qs : List ℕ) := (qs.foldl wordStep nums).getD (13+qs.length) 0

def Witness (i : Fin 65) (f g : Bool) (tail : List (Fin 8192)) :=
  tail.length ≤ 24 ∧ output (codes i f g tail)=2097151

/-- The posted proposition and the compact witness definition reduce to identical terms. -/
theorem instance_exact : (have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; have x2 : List ℕ → ℕ → List ℕ := fun (x2 : List ℕ) (x3 : ℕ) => x2 ++ [if x3 < (4096 : ℕ) then x2.getD (x3 % (64 : ℕ)) (0 : ℕ) &&& x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x2.getD (x3 % (64 : ℕ)) (0 : ℕ) ||| x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]; have x3 : ℕ → ℕ → Bool → ℕ := fun (x3 x4 : ℕ) (x5 : Bool) => x3 + (64 : ℕ) * x4 + if x5 = Bool.true then (4096 : ℕ) else (0 : ℕ); ∃ (x4 : Fin (65 : ℕ)) (x5 : Bool) (x6 : Bool) (x7 : List (Fin (8192 : ℕ))),   x7.length ≤ (24 : ℕ) ∧     have x8 : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑x4 / (13 : ℕ)) []).getD (↑x4 % (13 : ℕ)) (0 : ℕ);     have x9 : List ℕ := x3 (0 : ℕ) (↑(Fin.ofNat (14 : ℕ) (x8 / (225 : ℕ)))) x5 :: x3 (↑(Fin.ofNat (15 : ℕ) (x8 % (225 : ℕ) / (15 : ℕ)))) (↑(Fin.ofNat (15 : ℕ) (x8 % (15 : ℕ)))) x6 :: List.map Fin.val x7;     (List.foldl x2 x1 x9).getD ((13 : ℕ) + x9.length) (0 : ℕ) = (2097151 : ℕ)) ↔ ∃ i f g tail, Witness i f g tail := Iff.rfl

def decode (q : ℕ) : Op := ⟨decide (¬q<4096),q%64,q/64%64⟩
def gate (g : Op) : Gate := ⟨if g.isOr then .or else .and,[g.left,g.right]⟩
abbrev bits := PEqualNP.Outside.L_meta_3008_aux.step

private theorem readMap {α β : Type} (f : α → β) (xs : List α) (i : ℕ) (d : α) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  by_cases h : i<xs.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ h,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

private theorem wireMap {n} (s : State n) (g : Op) (z : Fin n → Bool) :
    (step s g).wires.map (fun w => w.full z) = bits (s.wires.map fun w => w.full z) (gate g) := by
  have l : (s.wires.map fun w => w.full z).getD g.left false = (s.wires.getD g.left default).full z :=
    readMap (fun w : Wire n => w.full z) _ _ default
  have r : (s.wires.map fun w => w.full z).getD g.right false = (s.wires.getD g.right default).full z :=
    readMap (fun w : Wire n => w.full z) _ _ default
  cases op : g.isOr <;> cases a : (s.wires.getD g.left default).pure <;>
    cases b : (s.wires.getD g.right default).pure <;>
    simp only [step,act,op,a,b,Bool.and_self,Bool.false_and,Bool.and_false,Bool.or_self,
      Bool.false_or,Bool.or_false,Bool.false_eq_true,ite_false,ite_true] <;>
    simp [joinW,meetW,cutW,bits,PEqualNP.Outside.L_meta_3008_aux.step,gate,op,GateOp.eval,l,r,-List.getD_eq_getElem?_getD]

private theorem wireFold {n} (s : State n) (gs : List Op) (z : Fin n → Bool) :
    (gs.foldl step s).wires.map (fun w => w.full z) = (gs.map gate).foldl bits (s.wires.map fun w => w.full z) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons,List.map_cons,List.foldl_cons,ih,wireMap]

private theorem wordMap (xs : List ℕ) (q r : ℕ) :
    (wordStep xs q).map (fun k => k.testBit r) = bits (xs.map fun k => k.testBit r) (gate (decode q)) := by
  have rd (i) : (xs.map fun k => k.testBit r).getD i false = (xs.getD i 0).testBit r := by
    simpa only [Nat.zero_testBit] using readMap (fun k : ℕ => k.testBit r) xs i 0
  by_cases lo : q<4096 <;>
    simp [wordStep,decode,gate,bits,PEqualNP.Outside.L_meta_3008_aux.step,GateOp.eval,lo,rd,-List.getD_eq_getElem?_getD]

private theorem wordFold (xs : List ℕ) (qs : List ℕ) (r : ℕ) :
    (qs.foldl wordStep xs).map (fun k => k.testBit r) =
      ((qs.map decode).map gate).foldl bits (xs.map fun k => k.testBit r) := by
  induction qs generalizing xs with
  | nil => rfl
  | cons q qs ih => rw [List.foldl_cons,List.map_cons,List.map_cons,List.foldl_cons,ih,wordMap]

theorem semantics (qs : List ℕ) (ok : output qs = 2097151) :
    ∀ z, ((run 14 (qs.map decode)).wires.getD (13+qs.length) default).full z = true ↔ predicate z := by
  let out := 13+qs.length
  let C : Circuit := ⟨(qs.map decode).map gate,out⟩
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hg
    cases h : a.isOr <;> simp [gate,h]
  have row (r : ℕ) : C.eval (nums.map fun k => k.testBit r) = (2097151 : ℕ).testBit r := by
    have h := congrArg (fun ws : List Bool => ws.getD out false) (wordFold nums qs r)
    have rd : ((qs.foldl wordStep nums).map fun k => k.testBit r).getD out false =
        (output qs).testBit r := by
      simpa only [Nat.zero_testBit,output,out] using readMap (fun k : ℕ => k.testBit r) (qs.foldl wordStep nums) out 0
    exact h.symm.trans (rd.trans (congrArg (fun k : ℕ => k.testBit r) ok))
  intro z
  have h := congrArg (fun ws : List Bool => ws.getD out false) (wireFold (initial 14) (qs.map decode) z)
  have rd := readMap (fun w : Wire 14 => w.full z) (run 14 (qs.map decode)).wires out default
  have first : (initial 14).wires.map (fun w => w.full z) = List.ofFn z := by
    simp [initial,atom]
  rw [first] at h
  have ev : ((run 14 (qs.map decode)).wires.getD out default).full z = C.eval (List.ofFn z) := rd.symm.trans h
  exact (ev ▸ PEqualNP.Outside.L_meta_3008 C mono row z)

theorem postedNecessary (i : Fin 65) (f g : Bool) (tail : List (Fin 8192)) (h : Witness i f g tail) :
    let qs := codes i f g tail
    let s := run 14 (qs.map decode)
    let w := s.wires.getD (13+qs.length) default
    none ∈ w.tags ∧ 1 ≤ s.dropped ∧ 3 ≤ missed w ∧ 3*(s.dropped+3) ≤ 4*missed w ∧
      (missed w=3 → (qs.map decode).length=26 ∧ s.dropped=1 ∧ w.jobs.card=6 ∧ s.bottom.length=12 ∧
        s.top.length=6 ∧ s.products.length+s.bypass=7) := by
  apply nestedNecessary _ _ (semantics _ h.2)
  have bound := h.1
  simp only [List.length_map,codes,List.length_cons]
  omega

#print axioms instance_exact
#print axioms semantics
#print axioms postedNecessary
end Checkpoint122.Posted
