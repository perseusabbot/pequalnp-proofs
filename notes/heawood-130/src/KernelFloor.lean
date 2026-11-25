import TwentyTwo
import ElevenLoss

namespace Checkpoint130.Heawood
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Prune
open PEqualNP.Outside.L_meta_3004_aux.Controls
open Checkpoint128

private def smallPort (m : ℕ) := [32,16,256,64,128,1,2,0,8,10,4].getD (five.signals.idxOf m) 0
private def upPos (r : ℕ) := [130,8194,129,257,136,2056,8208,2064,260,8196].getD (Theta.pos.idxOf r) 0
private def upNeg (r : ℕ) := [11648,3330,10241,9480,8201,400,282,3204,2055,148,31].getD (Theta.neg.idxOf r) 0

private theorem dataOK :
    (∀ m∈five.signals,smallPort m∈0::Theta.masks) ∧
    (∀ r∈Theta.pos,upPos r∈five.positives) ∧ (∀ r∈Theta.neg,upNeg r∈five.negatives) ∧
    (∀ m∈five.signals,∀ r∈Theta.pos,(m &&& upPos r != 0) → (smallPort m &&& r != 0)) ∧
    (∀ m∈five.signals,∀ r∈Theta.neg,(smallPort m &&& r != 0) → (m &&& upNeg r != 0)) ∧
    ∀ m∈five.signals,m≠1024 → (m &&& 1025 != 0) → (m &&& 31 != 0) := by decide +kernel

private def toTheta (m : Port) : Value Theta.Slot :=
  if h : smallPort m.val∈Theta.masks then .wire ⟨_,Theta.packMem h⟩ else .bit false

/-- Deleting vertex 10 gives the previously kernel-verified nine-vertex theta
test and saves one gate. The extra two-variable input maps to a legal theta port. -/
theorem fiveKernelFloor {gs : List (Binary.Tree Port)} {e} (hb : Built gs) (hr : Ready gs e)
    (ok : Fits valPos valNeg e) : 13≤gs.length := by
  obtain ⟨pal,yes,no,on,off,unique⟩ := dataOK
  let P (i : Fin Theta.width) (w : Theta.Slot) : Prop := w.val.testBit i.val=true
  let N (i : Fin Theta.width) (w : Theta.Slot) : Prop := w.val.testBit (Theta.width+i.val)=true
  let px (i : Fin Theta.width) : PosRow := ⟨_,yes _ (Theta.sampleRows i).1⟩
  let nx (i : Fin Theta.width) : NegRow := ⟨_,no _ (Theta.sampleRows i).2⟩
  have hi (i : Fin Theta.width) (m : Port) (h : valPos (px i) m) : (toTheta m).truth (P i) := by
    have good := on _ m.property _ (Theta.sampleRows i).1 h
    by_cases mem : smallPort m.val∈Theta.masks
    · simpa [toTheta,mem,Value.truth,P,(Theta.packBits mem i).1] using good
    · have zero := (List.mem_cons.mp (pal m.val m.property)).resolve_right mem
      simp [zero] at good
  have lo (i : Fin Theta.width) (m : Port) (h : (toTheta m).truth (N i)) : valNeg (nx i) m := by
    apply off _ m.property _ (Theta.sampleRows i).2
    by_cases mem : smallPort m.val∈Theta.masks
    · simpa [toTheta,mem,Value.truth,N,(Theta.packBits mem i).2] using h
    · simp [toTheta,mem,Value.truth] at h
  let removed : Port := ⟨1024,by decide +kernel⟩
  have needed : removed∈e.vars := mandatory ok removed ⟨1025,by decide +kernel⟩ ⟨31,by decide +kernel⟩
    (fun b diff => unique b.val b.property (fun eq => diff (Subtype.ext eq)))
  have zero : (toTheta removed).port=none := by decide +kernel
  obtain ⟨lib,t,good,ready,rows,cost⟩ := signedProjection hb hr ok toTheta P N px nx hi lo ⟨0,by decide⟩ ⟨0,by decide⟩
    {removed} (fun a ha => by obtain rfl := mem_singleton.mp ha; exact ⟨needed,zero⟩)
  have lower := Theta.localLower good ready (fun i => ⟨rows.1 i,rows.2 i⟩)
  simp only [card_singleton] at cost
  omega

/-- This lower bound uses only kernel-checked reductions and the kernel's
eleven-gate exhaustion of the theta test. -/
theorem nineteen {book : List (Binary.Tree V)} (built : Built book) {e} (ready : Ready book e)
    (truth : ∀ z : V→Bool,e.eval (fun v => z v=true) ↔ predicate z) : 19≤book.length := by
  obtain ⟨gs,t,hb,hr,ok,count⟩ := sixGateReduction built ready truth
  have lower := fiveKernelFloor hb hr ok
  omega

#print axioms fiveKernelFloor
#print axioms nineteen
end Checkpoint130.Heawood
