import RankCertificate
import Mathlib.Tactic.Abel

namespace Checkpoint134
open Finset
open PEqualNP.Outside.L_meta_9338 (V O Box tile side rm cm roll memSide rollBit maskSize
  legal hit fits containingTile encode readDigit)

abbrev Phase := Fin 3
abbrev Row := Fin 7
abbrev Cell := Fin 147
abbrev TileIndex := Fin 8435

def step (q : Phase) : V := ⟨7*q.val,by have := q.isLt; omega⟩
def emb (r : Row) : V := ⟨r.val,by have := r.isLt; omega⟩
def rowOf (x : Cell) : Row := ⟨x.val/21,by have := x.isLt; omega⟩
def colOf (x : Cell) : V := ⟨x.val%21,Nat.mod_lt _ (by decide)⟩
def Hit (b : Box) (i j : V) := ∃ q : Phase, hit b (i+step q) (j+step q)
def part (o : O) (s : Row) (i : Row) (q : Phase) : ℕ :=
  if (rm o).testBit ((emb i+step q-emb s).val) then roll (cm o) (emb s-step q) else 0
def rowMask (o : O) (s i : Row) := (part o s i 0 ||| part o s i 1 ||| part o s i 2) % 2097152
def code (o : O) (s : Row) := encode 2097152 7 (fun i => rowMask o s (Fin.ofNat 7 i))
def template (i : TileIndex) : O := ⟨i.val/7,by have := i.isLt; omega⟩
def shift (i : TileIndex) : Row := ⟨i.val%7,Nat.mod_lt _ (by decide)⟩
def masks (i : TileIndex) := code (template i) (shift i)

theorem rowRead (o : O) (s : Row) (z : Cell) :
    (code o s).testBit z.val = (rowMask o s (rowOf z)).testBit (colOf z).val := by
  have e := readDigit 2097152 7 (fun i => rowMask o s (Fin.ofNat 7 i))
    (fun _ _ => Nat.mod_lt _ (by decide)) (rowOf z).isLt
  change ((code o s / (2^21)^(rowOf z).val) % 2^21) = rowMask o s (Fin.ofNat 7 (rowOf z).val) at e
  have e' := congrArg (fun w : ℕ => w.testBit (colOf z).val) e
  rw [←pow_mul,←Nat.shiftRight_eq_div_pow] at e'
  have index : 21*(rowOf z).val+(colOf z).val=z.val := Nat.div_add_mod _ _
  simpa only [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,decide_eq_true (colOf z).isLt,
    Bool.true_and,index,Fin.ofNat_val_eq_self] using e'

theorem partHit {o : O} {s i : Row} {j : V} {q : Phase}
    (h : hit (tile o (emb s)) (emb i+step q) (j+step q)) :
    (part o s i q).testBit j.val=true := by
  obtain ⟨a,b⟩ := h
  have ar := (memSide (rm o) (emb s) (emb i+step q)).mp a
  have bc := (memSide (cm o) (emb s) (j+step q)).mp b
  have e : j-(emb s-step q)=j+step q-emb s := by abel
  simp only [part,ar,ite_true,rollBit _ (maskSize o).2,e,bc]

theorem codeHit {o : O} {s : Row} {z : Cell} (h : Hit (tile o (emb s)) (emb (rowOf z)) (colOf z)) :
    (code o s).testBit z.val=true := by
  obtain ⟨q,hq⟩ := h
  have v := partHit hq
  rw [rowRead]
  simp only [rowMask,show (2097152:ℕ)=2^21 from rfl,Nat.testBit_mod_two_pow,
    decide_eq_true (colOf z).isLt,Bool.true_and,Nat.testBit_or,Bool.or_eq_true]
  fin_cases q
  · exact Or.inl (Or.inl v)
  · exact Or.inl (Or.inr v)
  · exact Or.inr v

theorem projectTile (b : Box) (good : legal b) :
    ∃ idx : TileIndex, ∀ z : Cell, Hit b (emb (rowOf z)) (colOf z) → (masks idx).testBit z.val=true := by
  obtain ⟨o,s,sub⟩ := containingTile b.1 b.2 good
  let u : Row := ⟨s.val%7,Nat.mod_lt _ (by decide)⟩
  let idx : TileIndex := ⟨o.val*7+u.val,by have := o.isLt; have := u.isLt; omega⟩
  have t : template idx=o := by apply Fin.ext; change (o.val*7+u.val)/7=o.val; have := u.isLt; omega
  have p : shift idx=u := by apply Fin.ext; change (o.val*7+u.val)%7=u.val; have := u.isLt; omega
  have normalize : ∀ (a : V) (q : Phase), ∃ r : Phase, step q-a=step r-emb ⟨a.val%7,Nat.mod_lt _ (by decide)⟩ := by decide +kernel
  refine ⟨idx,?_⟩
  intro z hz
  obtain ⟨q,hr,hc⟩ := hz
  obtain ⟨r,hrq⟩ := normalize s q
  have e (v : V) : v+step q-s=v+step r-emb u := by simpa only [add_sub_assoc] using congrArg (v+·) hrq
  rw [masks,t,p]
  apply codeHit
  refine ⟨r,?_,?_⟩
  · apply (memSide ..).mpr
    rw [←e]
    exact (memSide ..).mp (sub.1 hr)
  · apply (memSide ..).mpr
    rw [←e]
    exact (memSide ..).mp (sub.2 hc)

#print axioms projectTile
end Checkpoint134
