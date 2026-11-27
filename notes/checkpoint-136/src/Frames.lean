import FrameCore

namespace Checkpoint136
open PEqualNP.Outside.L_meta_9338 (V bit)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def vec (a : List V) (i : V) : V := a.getD i.val 0
private def checkedPerm (p q : V → V) (l : ∀i,q (p i)=i) (r : ∀i,p (q i)=i) : Equiv.Perm V :=
  ⟨p,q,l,r⟩

private def r0 : Equiv.Perm V := checkedPerm (vec [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,0]) (vec [20,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]) (by decide) (by decide)
private def c0 : Equiv.Perm V := checkedPerm (vec [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,0]) (vec [20,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]) (by decide) (by decide)
def generator0 : Axis := ⟨(r0,c0),by change ∀i j,bit (r0 i) (c0 j)=bit i j; decide⟩
private def r1 : Equiv.Perm V := checkedPerm (vec [0,11,5,12,2,3,13,19,6,15,1,9,4,17,8,10,7,14,16,20,18]) (vec [0,10,4,5,12,2,8,16,14,11,15,1,3,6,17,9,18,13,20,7,19]) (by decide) (by decide)
private def c1 : Equiv.Perm V := checkedPerm (vec [7,10,12,19,2,20,18,5,11,1,8,9,3,13,15,6,14,0,16,4,17]) (vec [17,9,4,12,19,7,15,0,10,11,1,8,2,13,16,14,18,20,6,3,5]) (by decide) (by decide)
def generator1 : Axis := ⟨(r1,c1),by change ∀i j,bit (r1 i) (c1 j)=bit i j; decide⟩
private def r2 : Equiv.Perm V := checkedPerm (vec [0,2,4,6,8,10,12,14,16,18,20,1,3,5,7,9,11,13,15,17,19]) (vec [0,11,1,12,2,13,3,14,4,15,5,16,6,17,7,18,8,19,9,20,10]) (by decide) (by decide)
private def c2 : Equiv.Perm V := checkedPerm (vec [7,9,11,13,15,17,19,0,2,4,6,8,10,12,14,16,18,20,1,3,5]) (vec [7,18,8,19,9,20,10,0,11,1,12,2,13,3,14,4,15,5,16,6,17]) (by decide) (by decide)
def generator2 : Axis := ⟨(r2,c2),by change ∀i j,bit (r2 i) (c2 j)=bit i j; decide⟩

def baseGroup : Subgroup Axis := Subgroup.closure {generator0,generator1,generator2}
private def generator : Fin 3 → Axis | 0 => generator0 | 1 => generator1 | 2 => generator2
private def word : List (Fin 3) → Axis | [] => 1 | i::w => word w * generator i
private theorem wordMember (w : List (Fin 3)) : word w ∈ baseGroup := by
  induction w with
  | nil => exact baseGroup.one_mem
  | cons i w h =>
    apply baseGroup.mul_mem h
    apply Subgroup.subset_closure
    fin_cases i <;> simp [generator]

private def options0 : Finset V := ({0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20} : Finset V)
private def words0 : List (List (Fin 3)) := [[],[0],[0,0],[0,0,0],[0,0,2],[0,0,1],[0,0,0,2],[0,0,0,2,0],[0,0,2,2],[0,1,1],[0,0,1,2],[0,1],[0,1,0],[0,1,0,0],[0,1,0,0,0],[0,1,1,1],[0,0,2,2,2],[0,1,0,0,1],[0,1,1,2],[0,1,1,2,0],[0,0,1,2,2]]
private theorem reachable0 (v : V) (hv : v∈options0) :
    ∃g : fixing [],g.val∈baseGroup ∧ row g.val 0=v := by
  have good : ∀i : V, i∈options0 → (∀x∈([]:List V),row (word (words0.getD i.val [])) x=x) ∧
      row (word (words0.getD i.val [])) 0=i := by decide
  exact ⟨⟨_,(good v hv).1⟩,wordMember _,(good v hv).2⟩
private theorem upper0 (g : fixing []) : row g.val 0∈options0 := by
  have limited : ∀b : V, compatible [] [] 0 b → b∈options0 := by
    unfold compatible
    decide
  apply limited _ (imageCompatible g.val 0 ?_ ?_)
  · simp
  · simp

private def options1 : Finset V := ({1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20} : Finset V)
private def words1 : List (List (Fin 3)) := [[],[],[2],[2,1,1],[2,2],[2,1],[2,1,1,2],[1,1,2,1,1],[2,2,2],[1,1],[2,1,2],[1],[2,1,1,1],[2,1,1,2,1],[1,1,2,1,1,2],[1,1,1],[1,1,2,1],[2,1,1,2,1,1],[1,1,2],[2,1,2,2,2],[2,1,2,2]]
private theorem reachable1 (v : V) (hv : v∈options1) :
    ∃g : fixing [0],g.val∈baseGroup ∧ row g.val 1=v := by
  have good : ∀i : V, i∈options1 → (∀x∈([0]:List V),row (word (words1.getD i.val [])) x=x) ∧
      row (word (words1.getD i.val [])) 1=i := by decide
  exact ⟨⟨_,(good v hv).1⟩,wordMember _,(good v hv).2⟩
private theorem upper1 (g : fixing [0]) : row g.val 1∈options1 := by
  have hr0 : row g.val (0:V)=0 := g.property 0 (by decide)
  have limited : ∀b : V, compatible [0] [] 1 b → b∈options1 := by
    unfold compatible
    decide
  apply limited _ (imageCompatible g.val 1 ?_ ?_)
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl; assumption
  · simp

private def options2 : Finset V := ({2,3,5,6,7,8,9,10,11,12,13,15,17,18,19,20} : Finset V)
private def words2 : List (List (Fin 3)) := [[],[],[],[2,2,1,1,2,1],[],[0,0,1,0,1,2,2,2,0,2],[0,0,2,0,1,0,0,2,2,0],[0,0,1,2,2,2,1,0,2,1],[0,2,0,2,0,1,1,0,2,2],[0,1,2,2,1,2,2,0,1],[1,2],[0,0,0,2,0,1,1,0,2],[2,0,1,1,0,2,0,2],[0,0,2,0,2,2,1,0,0,0],[],[0,1,2,0,1,2,2,0,2,2],[],[2,2,2,1,1,2,2,1],[0,2,2,1,1,2,2,0,2],[1,2,1,1,1,2,1,1,1],[0,2,1,1,2,0,1,0,0,2]]
private theorem reachable2 (v : V) (hv : v∈options2) :
    ∃g : fixing [1,0],g.val∈baseGroup ∧ row g.val 2=v := by
  have good : ∀i : V, i∈options2 → (∀x∈([1,0]:List V),row (word (words2.getD i.val [])) x=x) ∧
      row (word (words2.getD i.val [])) 2=i := by decide
  exact ⟨⟨_,(good v hv).1⟩,wordMember _,(good v hv).2⟩
private theorem upper2 (g : fixing [1,0]) : row g.val 2∈options2 := by
  have hr1 : row g.val (1:V)=1 := g.property 1 (by decide)
  have hr0 : row g.val (0:V)=0 := g.property 0 (by decide)
  have hc0 : col g.val (0:V)=0 := fixedLine g.val hr0 hr1 (by decide) (by decide) (by decide)
  have limited : ∀b : V, compatible [0,1] [0] 2 b → b∈options2 := by
    unfold compatible
    decide
  apply limited _ (imageCompatible g.val 2 ?_ ?_)
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl <;> assumption
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl; assumption

private def options3 : Finset V := ({3,6,9,10,12,13,18,19,20} : Finset V)
private def words3 : List (List (Fin 3)) := [[],[],[],[],[],[],[0,2,0,1,1,0,2,2,0,2],[],[],[2,0,2,0,1,1,0,2,2,0],[1,1,2,2,2,1,1,1],[],[0,1,1,0,2,0,2,1,2,2],[0,1,0,0,0,0,1,2,0,1,1,2],[],[],[],[],[2,1,0,1,1,0,2,0,2,2],[1,1,2,2,1,1],[0,0,0,2,0,1,0,1,0,0,0,1]]
private theorem reachable3 (v : V) (hv : v∈options3) :
    ∃g : fixing [2,1,0],g.val∈baseGroup ∧ row g.val 3=v := by
  have good : ∀i : V, i∈options3 → (∀x∈([2,1,0]:List V),row (word (words3.getD i.val [])) x=x) ∧
      row (word (words3.getD i.val [])) 3=i := by decide
  exact ⟨⟨_,(good v hv).1⟩,wordMember _,(good v hv).2⟩
private theorem upper3 (g : fixing [2,1,0]) : row g.val 3∈options3 := by
  have hr2 : row g.val (2:V)=2 := g.property 2 (by decide)
  have hr1 : row g.val (1:V)=1 := g.property 1 (by decide)
  have hr0 : row g.val (0:V)=0 := g.property 0 (by decide)
  have hc0 : col g.val (0:V)=0 := fixedLine g.val hr0 hr1 (by decide) (by decide) (by decide)
  have hc7 : col g.val (7:V)=7 := fixedLine g.val hr0 hr2 (by decide) (by decide) (by decide)
  have hc1 : col g.val (1:V)=1 := fixedLine g.val hr1 hr2 (by decide) (by decide) (by decide)
  have limited : ∀b : V, compatible [0,1,2] [0,1,7] 3 b → b∈options3 := by
    unfold compatible
    decide
  apply limited _ (imageCompatible g.val 3 ?_ ?_)
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl <;> assumption

private def options4 : Finset V := ({4,14} : Finset V)
private def words4 : List (List (Fin 3)) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1,1,1,2,1,1,1],[],[],[],[],[],[]]
private theorem reachable4 (v : V) (hv : v∈options4) :
    ∃g : fixing [3,2,1,0],g.val∈baseGroup ∧ row g.val 4=v := by
  have good : ∀i : V, i∈options4 → (∀x∈([3,2,1,0]:List V),row (word (words4.getD i.val [])) x=x) ∧
      row (word (words4.getD i.val [])) 4=i := by decide
  exact ⟨⟨_,(good v hv).1⟩,wordMember _,(good v hv).2⟩
private theorem upper4 (g : fixing [3,2,1,0]) : row g.val 4∈options4 := by
  have hr3 : row g.val (3:V)=3 := g.property 3 (by decide)
  have hr2 : row g.val (2:V)=2 := g.property 2 (by decide)
  have hr1 : row g.val (1:V)=1 := g.property 1 (by decide)
  have hr0 : row g.val (0:V)=0 := g.property 0 (by decide)
  have hc0 : col g.val (0:V)=0 := fixedLine g.val hr0 hr1 (by decide) (by decide) (by decide)
  have hc7 : col g.val (7:V)=7 := fixedLine g.val hr0 hr2 (by decide) (by decide) (by decide)
  have hc20 : col g.val (20:V)=20 := fixedLine g.val hr0 hr3 (by decide) (by decide) (by decide)
  have hc1 : col g.val (1:V)=1 := fixedLine g.val hr1 hr2 (by decide) (by decide) (by decide)
  have hc8 : col g.val (8:V)=8 := fixedLine g.val hr1 hr3 (by decide) (by decide) (by decide)
  have hc2 : col g.val (2:V)=2 := fixedLine g.val hr2 hr3 (by decide) (by decide) (by decide)
  have hr16 : row g.val (16:V)=16 := fixedPoint g.val hc0 hc2 (by decide) (by decide) (by decide)
  have hr15 : row g.val (15:V)=15 := fixedPoint g.val hc1 hc20 (by decide) (by decide) (by decide)
  have hr8 : row g.val (8:V)=8 := fixedPoint g.val hc7 hc8 (by decide) (by decide) (by decide)
  have hc15 : col g.val (15:V)=15 := fixedLine g.val hr8 hr15 (by decide) (by decide) (by decide)
  have limited : ∀b : V, compatible [0,1,2,3,8,15,16] [0,1,2,7,8,15,20] 4 b → b∈options4 := by
    unfold compatible
    decide
  apply limited _ (imageCompatible g.val 4 ?_ ?_)
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem lastIdentity (g : fixing [4,3,2,1,0]) : g.val=1 := by
  have hr4 : row g.val (4:V)=4 := g.property 4 (by decide)
  have hr3 : row g.val (3:V)=3 := g.property 3 (by decide)
  have hr2 : row g.val (2:V)=2 := g.property 2 (by decide)
  have hr1 : row g.val (1:V)=1 := g.property 1 (by decide)
  have hr0 : row g.val (0:V)=0 := g.property 0 (by decide)
  have hc0 : col g.val (0:V)=0 := fixedLine g.val hr0 hr1 (by decide) (by decide) (by decide)
  have hc7 : col g.val (7:V)=7 := fixedLine g.val hr0 hr2 (by decide) (by decide) (by decide)
  have hc20 : col g.val (20:V)=20 := fixedLine g.val hr0 hr3 (by decide) (by decide) (by decide)
  have hc1 : col g.val (1:V)=1 := fixedLine g.val hr1 hr2 (by decide) (by decide) (by decide)
  have hc8 : col g.val (8:V)=8 := fixedLine g.val hr1 hr3 (by decide) (by decide) (by decide)
  have hc2 : col g.val (2:V)=2 := fixedLine g.val hr2 hr3 (by decide) (by decide) (by decide)
  have hc9 : col g.val (9:V)=9 := fixedLine g.val hr2 hr4 (by decide) (by decide) (by decide)
  have hc3 : col g.val (3:V)=3 := fixedLine g.val hr3 hr4 (by decide) (by decide) (by decide)
  have hr16 : row g.val (16:V)=16 := fixedPoint g.val hc0 hc2 (by decide) (by decide) (by decide)
  have hr17 : row g.val (17:V)=17 := fixedPoint g.val hc1 hc3 (by decide) (by decide) (by decide)
  have hr15 : row g.val (15:V)=15 := fixedPoint g.val hc1 hc20 (by decide) (by decide) (by decide)
  have hr7 : row g.val (7:V)=7 := fixedPoint g.val hc3 hc7 (by decide) (by decide) (by decide)
  have hr8 : row g.val (8:V)=8 := fixedPoint g.val hc7 hc8 (by decide) (by decide) (by decide)
  have hr9 : row g.val (9:V)=9 := fixedPoint g.val hc8 hc9 (by decide) (by decide) (by decide)
  have hr13 : row g.val (13:V)=13 := fixedPoint g.val hc9 hc20 (by decide) (by decide) (by decide)
  have hc5 : col g.val (5:V)=5 := fixedLine g.val hr0 hr9 (by decide) (by decide) (by decide)
  have hc17 : col g.val (17:V)=17 := fixedLine g.val hr0 hr17 (by decide) (by decide) (by decide)
  have hc6 : col g.val (6:V)=6 := fixedLine g.val hr1 hr7 (by decide) (by decide) (by decide)
  have hc18 : col g.val (18:V)=18 := fixedLine g.val hr1 hr13 (by decide) (by decide) (by decide)
  have hc4 : col g.val (4:V)=4 := fixedLine g.val hr4 hr8 (by decide) (by decide) (by decide)
  have hc11 : col g.val (11:V)=11 := fixedLine g.val hr4 hr15 (by decide) (by decide) (by decide)
  have hc14 : col g.val (14:V)=14 := fixedLine g.val hr7 hr9 (by decide) (by decide) (by decide)
  have hc12 : col g.val (12:V)=12 := fixedLine g.val hr7 hr13 (by decide) (by decide) (by decide)
  have hc13 : col g.val (13:V)=13 := fixedLine g.val hr8 hr13 (by decide) (by decide) (by decide)
  have hc15 : col g.val (15:V)=15 := fixedLine g.val hr8 hr15 (by decide) (by decide) (by decide)
  have hc16 : col g.val (16:V)=16 := fixedLine g.val hr9 hr16 (by decide) (by decide) (by decide)
  have hr14 : row g.val (14:V)=14 := fixedPoint g.val hc0 hc13 (by decide) (by decide) (by decide)
  have hr5 : row g.val (5:V)=5 := fixedPoint g.val hc1 hc4 (by decide) (by decide) (by decide)
  have hr18 : row g.val (18:V)=18 := fixedPoint g.val hc2 hc4 (by decide) (by decide) (by decide)
  have hr6 : row g.val (6:V)=6 := fixedPoint g.val hc2 hc5 (by decide) (by decide) (by decide)
  have hr19 : row g.val (19:V)=19 := fixedPoint g.val hc3 hc5 (by decide) (by decide) (by decide)
  have hr20 : row g.val (20:V)=20 := fixedPoint g.val hc4 hc6 (by decide) (by decide) (by decide)
  have hr10 : row g.val (10:V)=10 := fixedPoint g.val hc6 hc9 (by decide) (by decide) (by decide)
  have hr11 : row g.val (11:V)=11 := fixedPoint g.val hc7 hc11 (by decide) (by decide) (by decide)
  have hr12 : row g.val (12:V)=12 := fixedPoint g.val hc8 hc11 (by decide) (by decide) (by decide)
  have hc19 : col g.val (19:V)=19 := fixedLine g.val hr2 hr12 (by decide) (by decide) (by decide)
  have hc10 : col g.val (10:V)=10 := fixedLine g.val hr3 hr5 (by decide) (by decide) (by decide)
  apply Subtype.ext
  apply Prod.ext
  · apply Equiv.ext; intro i; fin_cases i <;> assumption
  · apply Equiv.ext; intro i; fin_cases i <;> assumption

/-- The full axis-preserving symmetry group of the posted matrix. -/
theorem collineationCount : Nat.card Axis=120960 := by
  let : Subsingleton (fixing [4,3,2,1,0]) := ⟨fun x y => Subtype.ext ((lastIdentity x).trans (lastIdentity y).symm)⟩
  rw [emptyCard]
  rw [stepCard [] 0 options0 upper0 (fun v h => (reachable0 v h).imp fun _ q => q.2)]
  rw [stepCard [0] 1 options1 upper1 (fun v h => (reachable1 v h).imp fun _ q => q.2)]
  rw [stepCard [1,0] 2 options2 upper2 (fun v h => (reachable2 v h).imp fun _ q => q.2)]
  rw [stepCard [2,1,0] 3 options3 upper3 (fun v h => (reachable3 v h).imp fun _ q => q.2)]
  rw [stepCard [3,2,1,0] 4 options4 upper4 (fun v h => (reachable4 v h).imp fun _ q => q.2)]
  rw [Nat.card_unique]
  decide

/-- Three previously published axis maps generate every collineation. -/
theorem generatorsComplete : baseGroup=⊤ := by
  apply top_unique
  intro f _
  have enumerate : ∀g : fixing [],g.val∈baseGroup := by
    apply extendMembership (a:=0) (fun g => reachable0 _ (upper0 g))
    apply extendMembership (a:=1) (fun g => reachable1 _ (upper1 g))
    apply extendMembership (a:=2) (fun g => reachable2 _ (upper2 g))
    apply extendMembership (a:=3) (fun g => reachable3 _ (upper3 g))
    apply extendMembership (a:=4) (fun g => reachable4 _ (upper4 g))
    intro g; rw [lastIdentity]; exact baseGroup.one_mem
  exact enumerate ⟨f,by simp [fixing]⟩

abbrev Dual := {g : Equiv.Perm V × Equiv.Perm V // ∀i j,bit (g.1 j) (g.2 i)=bit i j}
private def reverseAxis : Equiv.Perm V := checkedPerm (vec [0,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1])
  (vec [0,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1]) (by decide) (by decide)
private theorem reverseBoard : ∀i j,bit (reverseAxis j) (reverseAxis i)=bit i j := by decide
private theorem reverseTwice : ∀i,reverseAxis (reverseAxis i)=i := by decide
def toDual : Axis ≃ Dual where
  toFun g := ⟨(row g*reverseAxis,col g*reverseAxis),fun i j => (g.property _ _).trans (reverseBoard i j)⟩
  invFun g := ⟨(g.val.1*reverseAxis,g.val.2*reverseAxis),fun i j => (g.property (reverseAxis j) (reverseAxis i)).trans (reverseBoard i j)⟩
  left_inv g := by
    apply Subtype.ext; apply Prod.ext <;> apply Equiv.ext <;> intro x <;> simp only [row,col,Equiv.Perm.mul_apply,reverseTwice]
  right_inv g := by
    apply Subtype.ext; apply Prod.ext <;> apply Equiv.ext <;> intro x <;> simp only [row,col,Equiv.Perm.mul_apply,reverseTwice]

/-- A symmetry either preserves both shores or exchanges them. -/
theorem fullBoardCount : Nat.card (Sum Axis Dual)=241920 := by
  rw [Nat.card_sum,← Nat.card_congr toDual,collineationCount]

#print axioms collineationCount
#print axioms generatorsComplete
#print axioms fullBoardCount
end Checkpoint136
