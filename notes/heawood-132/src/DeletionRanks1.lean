import DeletionRanks0

namespace Checkpoint132.Induced

private def choicesrank963 : List Choice := [
  ⟨129,129,1,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨834,387,4,14,[13,8,9,12,11,10,7,2,1,0,4,3,5,6]⟩]
private def lookuprank963 : List ℕ := [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,1,1,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank963 : Floor 963 7 := by
  apply certified choicesrank963 lookuprank963
  · intro r hr
    simp only [choicesrank963,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact floorMono rank129 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
  · have good : choicesrank963.all (fun r => decide (Verified 963 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank967 : List Choice := [
  ⟨389,387,4,14,[0,2,1,6,4,5,3,8,7,12,10,11,9,13]⟩,
  ⟨966,903,7,14,[13,8,9,12,11,10,7,2,1,0,4,3,5,6]⟩,
  ⟨963,963,7,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨836,387,4,7,[3,6,1,4,5,2,0,11,7,8,12,10,13,9]⟩,
  ⟨643,387,4,14,[8,7,12,10,11,9,13,0,2,1,6,4,5,3]⟩,
  ⟨965,907,7,14,[0,6,3,2,4,5,1,8,7,9,10,13,12,11]⟩,
  ⟨389,387,4,9,[0,2,1,6,4,5,3,8,7,12,10,11,9,13]⟩,
  ⟨903,903,7,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩]
private def lookuprank967 : List ℕ := [0,0,1,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,2,0,0,0,0,0,4,0,0,0,0,0,1,0,2,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1,1,1,1,0,0,0,0,1,0,2,0,0,0,0,3,5,0,0,0,0,0,1,2,0,0,0,0,7,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,7,0,0,0,0,3,4,0,0,0,0,0,1,3,2,0,0,0,3,0,3,3,0,0,0,0,1,5,2,0,0,0,4,3,0,6,0,0,0,0,1,0,2,0,0,0,0,3,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank967 : Floor 967 9 := by
  apply certified choicesrank967 lookuprank967
  · intro r hr
    simp only [choicesrank967,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
    · exact floorMono rank963 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank907 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
  · have good : choicesrank967.all (fun r => decide (Verified 967 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank3770 : List Choice := [
  ⟨650,387,4,14,[10,7,11,8,12,9,13,0,4,1,5,2,6,3]⟩,
  ⟨3256,903,7,14,[13,12,11,8,7,9,10,2,4,5,1,0,6,3]⟩,
  ⟨3634,903,7,14,[3,2,4,5,1,0,6,12,11,8,7,9,10,13]⟩]
private def lookuprank3770 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,2,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,1,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,2,2,0,2,0,1,2,2,0,0,0,1,0,2,0,0,0,2,0,1,0,0,0,0,0,1,0,2,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,2,2,2,0,0,0,1,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,1,1,0,1,0,0,1,1,0,0,0,1,0,2,0,0,0,2,0,1,0,0,0,0,0,1,0,2,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank3770 : Floor 3770 10 := by
  apply certified choicesrank3770 lookuprank3770
  · intro r hr
    simp only [choicesrank3770,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
  · have good : choicesrank3770.all (fun r => decide (Verified 3770 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank2030 : List Choice := [
  ⟨994,907,7,14,[6,0,5,2,4,3,1,8,9,7,11,13,12,10]⟩,
  ⟨650,387,4,14,[10,7,11,8,12,9,13,0,4,1,5,2,6,3]⟩,
  ⟨1892,903,7,14,[13,10,9,11,12,8,7,4,1,0,2,3,6,5]⟩,
  ⟨864,387,4,7,[2,3,6,5,4,1,0,12,8,7,13,10,9,11]⟩,
  ⟨1706,903,7,14,[13,7,11,9,12,8,10,1,4,0,2,5,6,3]⟩,
  ⟨650,387,4,8,[10,7,11,8,12,9,13,0,4,1,5,2,6,3]⟩,
  ⟨966,903,7,10,[13,8,9,12,11,10,7,2,1,0,4,3,5,6]⟩,
  ⟨966,903,7,14,[13,8,9,12,11,10,7,2,1,0,4,3,5,6]⟩]
private def lookuprank2030 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,2,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,1,1,0,0,0,0,0,1,0,0,0,1,0,1,1,1,0,0,0,0,0,2,0,0,0,1,1,0,1,2,0,0,0,0,0,1,0,0,0,1,1,1,0,1,0,0,0,0,0,2,0,0,0,1,1,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,2,2,2,2,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,1,2,1,6,0,0,0,0,0,2,4,0,0,1,0,2,1,4,0,0,0,0,0,2,0,0,0,2,2,0,2,2,0,0,0,0,0,2,0,0,0,1,1,2,0,4,0,0,0,0,0,2,0,0,0,6,4,2,4,0,6,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank2030 : Floor 2030 11 := by
  apply certified choicesrank2030 lookuprank2030
  · intro r hr
    simp only [choicesrank2030,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank907 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
    · exact floorMono rank387 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
  · have good : choicesrank2030.all (fun r => decide (Verified 2030 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

#print axioms rank963
#print axioms rank967
#print axioms rank3770
#print axioms rank2030
end Checkpoint132.Induced
