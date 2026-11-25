import DeletionRanks1

namespace Checkpoint132.Induced

private def choicesrank2031 : List Choice := [
  ⟨967,967,9,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨1707,967,9,14,[0,6,4,2,3,1,5,8,10,9,7,12,13,11]⟩,
  ⟨1893,967,9,14,[0,5,2,4,3,1,6,10,8,9,7,11,13,12]⟩,
  ⟨2030,2030,11,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨1421,907,7,9,[7,10,9,8,12,11,13,0,1,4,3,2,6,5]⟩]
private def lookuprank2031 : List ℕ := [0,2,1,0,0,0,1,2,1,3,0,0,0,0,2,0,1,0,0,0,1,2,1,2,0,0,0,0,1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,1,1,1,0,0,0,0,2,2,1,0,0,0,1,0,1,2,0,0,0,0,1,1,1,0,0,0,1,1,0,1,0,0,0,0,3,2,1,0,0,0,1,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,3,0,0,1,2,1,3,0,0,0,0,2,0,1,2,0,0,1,2,1,2,0,0,0,0,3,1,0,0,0,0,1,1,1,1,0,0,0,0,3,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,1,1,1,0,0,0,0,2,2,1,0,0,0,1,0,1,2,0,0,0,0,1,1,1,0,0,0,1,1,0,1,0,0,0,0,3,2,1,0,0,0,1,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank2031 : Floor 2031 13 := by
  apply certified choicesrank2031 lookuprank2031
  · intro r hr
    simp only [choicesrank2031,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank2030 (by decide +kernel)
    · exact floorMono rank907 (by decide +kernel)
  · have good : choicesrank2031.all (fun r => decide (Verified 2031 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank4027 : List Choice := [
  ⟨1707,967,9,14,[0,6,4,2,3,1,5,8,10,9,7,12,13,11]⟩,
  ⟨3481,967,9,14,[8,10,12,7,9,11,13,0,2,4,6,1,3,5]⟩,
  ⟨3634,903,7,14,[3,2,4,5,1,0,6,12,11,8,7,9,10,13]⟩,
  ⟨3003,2030,11,14,[5,1,4,6,2,3,0,9,10,7,12,8,11,13]⟩,
  ⟨1433,907,7,9,[7,10,12,8,9,13,11,0,3,4,1,6,2,5]⟩,
  ⟨3770,3770,10,8,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩]
private def lookuprank4027 : List ℕ := [0,1,0,2,0,1,0,2,0,1,2,0,0,0,1,0,0,1,0,1,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,0,0,1,0,2,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,2,0,1,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,1,0,1,0,0,1,0,0,0,2,1,0,2,0,1,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,2,0,1,0,2,0,1,3,0,0,0,1,0,0,1,0,1,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,0,0,1,0,2,0,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,2,0,1,0,0,5,1,3,0,0,0,0,0,0,0,0,0,0,5,0,0,3,0,0,0,1,1,0,1,0,1,0,1,0,0,1,0,0,0,3,1,0,3,0,1,0,3,3,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank4027 : Floor 4027 13 := by
  apply certified choicesrank4027 lookuprank4027
  · intro r hr
    simp only [choicesrank4027,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
    · exact floorMono rank2030 (by decide +kernel)
    · exact floorMono rank907 (by decide +kernel)
    · exact floorMono rank3770 (by decide +kernel)
  · have good : choicesrank4027.all (fun r => decide (Verified 4027 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank4059 : List Choice := [
  ⟨1987,967,9,14,[8,7,11,10,12,13,9,0,6,1,2,5,4,3]⟩,
  ⟨2521,967,9,14,[1,3,5,0,2,4,6,7,9,11,13,8,10,12]⟩,
  ⟨2778,967,9,14,[3,1,4,0,2,5,6,7,11,9,12,8,10,13]⟩,
  ⟨3353,903,7,14,[1,4,5,2,0,3,6,13,9,11,7,8,12,10]⟩]
private def lookuprank4059 : List ℕ := [0,1,0,0,0,0,2,2,2,1,1,0,0,0,1,0,0,0,0,0,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,0,0,0,0,3,2,1,1,0,0,0,2,1,0,0,0,0,3,0,2,1,1,0,0,0,2,1,0,0,0,0,2,2,0,1,1,0,0,0,1,1,0,0,0,0,1,1,1,0,1,0,0,0,1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,2,2,2,1,1,0,0,0,1,0,0,0,0,0,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,0,0,0,0,3,2,1,1,0,0,0,2,1,0,0,0,0,3,0,2,1,1,0,0,0,2,1,0,0,0,0,2,2,0,1,1,0,0,0,1,1,0,0,0,0,1,1,1,0,1,0,0,0,1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank4059 : Floor 4059 13 := by
  apply certified choicesrank4059 lookuprank4059
  · intro r hr
    simp only [choicesrank4059,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank903 (by decide +kernel)
  · have good : choicesrank4059.all (fun r => decide (Verified 4059 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank4091 : List Choice := [
  ⟨971,967,9,14,[0,6,3,2,4,5,1,8,7,9,10,13,12,11]⟩,
  ⟨3257,967,9,14,[0,3,4,1,6,2,5,7,10,12,8,9,13,11]⟩,
  ⟨3963,2031,13,14,[5,2,4,3,1,6,0,12,10,8,9,7,11,13]⟩,
  ⟨4083,4059,13,14,[0,4,2,5,1,3,6,10,8,11,7,9,12,13]⟩,
  ⟨4090,4027,13,14,[6,1,2,5,4,3,0,9,8,7,11,10,12,13]⟩,
  ⟨971,967,9,4,[0,6,3,2,4,5,1,8,7,9,10,13,12,11]⟩,
  ⟨2521,967,9,14,[1,3,5,0,2,4,6,7,9,11,13,8,10,12]⟩,
  ⟨2043,2031,13,14,[0,1,4,3,2,6,5,7,10,9,8,12,11,13]⟩,
  ⟨2507,967,9,5,[0,2,3,6,5,4,1,8,7,13,10,9,11,12]⟩,
  ⟨3018,967,9,10,[13,7,12,9,11,10,8,1,2,0,4,6,5,3]⟩]
private def lookuprank4091 : List ℕ := [0,1,0,3,0,0,1,2,1,1,0,0,0,0,1,0,0,1,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,1,0,0,0,0,1,2,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,1,1,1,0,0,0,0,2,1,0,2,0,0,1,0,1,1,0,0,0,0,1,1,0,1,0,0,1,1,0,1,0,0,0,0,1,1,0,1,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,3,4,4,4,2,4,4,4,4,0,0,4,0,0,3,5,6,1,2,1,1,6,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,0,0,3,3,3,2,3,3,3,3,0,0,4,5,0,3,0,0,5,2,5,5,0,0,0,0,4,6,0,3,0,0,8,2,8,6,0,0,0,0,4,1,0,3,5,8,0,2,1,1,9,7,0,0,2,2,0,2,2,2,2,0,2,2,2,2,0,0,4,1,0,3,5,8,1,2,0,1,9,7,0,0,4,1,0,3,5,6,1,2,1,0,6,7,0,0,4,6,0,3,0,0,9,2,9,6,0,0,0,0,4,7,0,3,0,0,7,2,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank4091 : Floor 4091 15 := by
  apply certified choicesrank4091 lookuprank4091
  · intro r hr
    simp only [choicesrank4091,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank2031 (by decide +kernel)
    · exact floorMono rank4059 (by decide +kernel)
    · exact floorMono rank4027 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank2031 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
  · have good : choicesrank4091.all (fun r => decide (Verified 4091 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

#print axioms rank2031
#print axioms rank4027
#print axioms rank4059
#print axioms rank4091
end Checkpoint132.Induced
