import InducedCertificate

namespace Checkpoint132.Induced

theorem rank129 : Floor 129 1 := inputFloor (by decide +kernel) (by decide +kernel)

private def choicesrank387 : List Choice := [
  ⟨129,129,1,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨130,129,1,14,[8,7,12,10,11,9,13,0,2,1,6,4,5,3]⟩,
  ⟨130,129,1,8,[8,7,12,10,11,9,13,0,2,1,6,4,5,3]⟩]
private def lookuprank387 : List ℕ := [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank387 : Floor 387 4 := by
  apply certified choicesrank387 lookuprank387
  · intro r hr
    simp only [choicesrank387,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact floorMono rank129 (by decide +kernel)
    · exact floorMono rank129 (by decide +kernel)
    · exact floorMono rank129 (by decide +kernel)
  · have good : choicesrank387.all (fun r => decide (Verified 387 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank903 : List Choice := [
  ⟨129,129,1,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨260,129,1,14,[1,5,0,6,4,2,3,9,7,12,13,11,8,10]⟩,
  ⟨514,129,1,14,[9,7,12,13,11,8,10,1,5,0,6,4,2,3]⟩,
  ⟨387,387,4,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨389,387,4,9,[0,2,1,6,4,5,3,8,7,12,10,11,9,13]⟩,
  ⟨643,387,4,2,[8,7,12,10,11,9,13,0,2,1,6,4,5,3]⟩]
private def lookuprank903 : List ℕ := [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,5,0,0,0,0,1,2,1,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,5,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,2,0,0,0,0,0,2,4,0,0,0,0,2,0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank903 : Floor 903 7 := by
  apply certified choicesrank903 lookuprank903
  · intro r hr
    simp only [choicesrank903,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank129 (by decide +kernel)
    · exact floorMono rank129 (by decide +kernel)
    · exact floorMono rank129 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
  · have good : choicesrank903.all (fun r => decide (Verified 903 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank907 : List Choice := [
  ⟨136,129,1,14,[8,10,12,7,9,11,13,0,2,4,6,1,3,5]⟩,
  ⟨387,387,4,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨650,387,4,14,[10,7,11,8,12,9,13,0,4,1,5,2,6,3]⟩,
  ⟨393,387,4,14,[0,3,2,1,5,4,6,7,8,11,10,9,13,12]⟩,
  ⟨393,387,4,9,[0,3,2,1,5,4,6,7,8,11,10,9,13,12]⟩,
  ⟨650,387,4,8,[10,7,11,8,12,9,13,0,4,1,5,2,6,3]⟩]
private def lookuprank907 : List ℕ := [0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,0,1,0,0,0,0,5,4,0,0,0,0,0,0,0,1,0,0,0,5,0,0,0,0,0,0,0,0,0,1,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank907 : Floor 907 7 := by
  apply certified choicesrank907 lookuprank907
  · intro r hr
    simp only [choicesrank907,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank129 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
  · have good : choicesrank907.all (fun r => decide (Verified 907 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

#print axioms rank129
#print axioms rank387
#print axioms rank903
#print axioms rank907
end Checkpoint132.Induced
