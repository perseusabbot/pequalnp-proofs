import OpeningRows132

namespace Checkpoint132.Opening
open Checkpoint122.Posted Checkpoint132.Word
open PEqualNP.Outside.L_meta_3008_aux (nums)

def result (columns qs : List ℕ) := (qs.foldl wordStep columns).getD (15+qs.length) 0

private theorem finishBits (qs : List ℕ) (safe : avoidsCenter qs) (ok : result localBase qs=262143) :
    (result base qs ||| overlay)=2097151 := by
  have atResult {R : ℕ→ℕ→Prop} {x y : List ℕ}
      (h : Tracks R (qs.foldl wordStep x) (qs.foldl wordStep y)) : R (result x qs) (result y qs) :=
    h.2 _ (by omega)
  have width : result base qs<2^58 := by
    apply atResult (x:=base) (y:=base) (R:=fun _ b => b<2^58)
    apply propagate (by decide +kernel) (fun _ right => Nat.and_lt_two_pow _ right) Nat.or_lt_two_pow qs safe
    exact start dimensions.1 dimensions.1 (by decide +kernel) (fun v _ => boundedBase v)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (2097151 : ℕ)=2^21-1 from rfl,Nat.testBit_two_pow_sub_one,Nat.testBit_or]
  by_cases small : i<21
  · rw [decide_eq_true small,Bool.or_eq_true]
    rcases positiveLinks ⟨i,small⟩ with hit|⟨lt,link⟩
    · exact Or.inr hit
    · have val : BitLE (posLink.getD i 0) i (result localBase qs) (result base qs) :=
        atResult (bits qs safe (start dimensions.2.1 dimensions.1 (by simp [BitLE]) link))
      apply Or.inl
      apply val
      rw [ok,show (262143 : ℕ)=2^18-1 from rfl,Nat.testBit_two_pow_sub_one]
      exact decide_eq_true lt
  · rw [decide_eq_false small,Bool.or_eq_false_iff]
    by_cases middle : i<58
    · let j : Fin 37 := ⟨i-21,by omega⟩
      have idx : 21+j.val=i := by dsimp [j]; omega
      obtain ⟨off,limit,link⟩ := negativeLinks j
      rw [idx] at off link
      refine ⟨?_,off⟩
      apply Bool.eq_false_iff.mpr
      intro accepted
      have val : BitLE i (negLink.getD j.val 0) (result base qs) (result localBase qs) :=
        atResult (bits qs safe (start dimensions.1 dimensions.2.1 (by simp [BitLE]) link))
      have bad := val accepted
      rw [ok,show (262143 : ℕ)=2^18-1 from rfl,Nat.testBit_two_pow_sub_one,
        decide_eq_false (Nat.not_lt.mpr limit)] at bad
      contradiction
    · have upper : (2:ℕ)^58≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
      exact ⟨Nat.testBit_lt_two_pow (width.trans_le upper),Nat.testBit_lt_two_pow (dimensions.2.2.trans_le upper)⟩

def finish (qs : List (Fin 8192)) (limit : qs.length≤22) : List (Fin 8192) :=
  qs++[⟨967,by decide⟩,⟨15+qs.length+64*(16+qs.length)+4096,by omega⟩]

private theorem lastAppend (w : List ℕ) (z : ℕ) : (w++[z]).getD w.length 0=z := by
  rw [List.getD_append_right _ _ _ _ le_rfl]; simp

private theorem finishOutput (ops : List (Fin 8192)) (limit : ops.length≤22) :
    output (codes 20 true true (finish ops limit))=result base (ops.map Fin.val) ||| overlay := by
  let qs := ops.map Fin.val
  let k := ops.length
  let w := qs.foldl wordStep base
  have n : qs.length=k := by simp [qs,k]
  have size : w.length=16+k := by rw [show w=qs.foldl wordStep base from rfl,sizes,dimensions.1,n]
  have early (v : ℕ) (hv : v<16) : w.getD v 0=base.getD v 0 :=
    unchanged qs base v (dimensions.1 ▸ hv)
  have prod : wordStep w 967=w++[overlay] := by
    change w++[w.getD 7 0 &&& w.getD 15 0]=w++[base.getD 7 0 &&& base.getD 15 0]
    rw [early 7 (by decide),early 15 (by decide)]
  let q := 15+k+64*(16+k)+4096
  have left : q%64=15+k := by dsimp [q,k]; omega
  have right : q/64%64=16+k := by
    change (15+ops.length+64*(16+ops.length)+4096)/64%64=16+ops.length
    interval_cases h : ops.length <;> decide +kernel
  have op : ¬q<4096 := by dsimp [q]; omega
  have program : codes 20 true true (finish ops limit)=codes 20 true true []++qs++[967,q] := by
    simp [codes,finish,qs,q,k]
  unfold output
  rw [program]
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (wordStep (wordStep w 967) q).getD (13+(codes 20 true true []++qs++[967,q]).length) 0=_
  have last : 13+(codes 20 true true []++qs++[967,q]).length=(w++[overlay]).length := by
    simp only [List.length_append,List.length_cons,List.length_nil,n,size]
    have pre : (codes 20 true true []).length=2 := rfl
    omega
  rw [prod,last]
  change ((w++[overlay])++[value (w++[overlay]) q]).getD (w++[overlay]).length 0=_
  rw [lastAppend]
  simp only [value,ite_eq_right op,left,right,List.getD_append _ _ _ _ (show 15+k<w.length by omega),
    ←size,lastAppend]
  change w.getD (15+k) 0 ||| overlay=w.getD (15+qs.length) 0 ||| overlay
  rw [n]

/-- A 22-gate local solution in the posted wire numbering yields a witness for opening 20.
The center is absent from the local problem. The last two instructions add its three incident edges. -/
theorem postedWitness (ops : List (Fin 8192)) (limit : ops.length≤22)
    (safe : avoidsCenter (ops.map Fin.val)) (ok : result localBase (ops.map Fin.val)=262143) :
    Witness 20 true true (finish ops limit) := by
  refine ⟨?_,(finishOutput ops limit).trans (finishBits _ safe ok)⟩
  simp only [finish,List.length_append,List.length_cons,List.length_nil]
  omega

#print axioms postedWitness
end Checkpoint132.Opening
