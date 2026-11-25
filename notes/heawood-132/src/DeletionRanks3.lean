import DeletionRanks2

namespace Checkpoint132.Induced

private def choicesrank8127 : List Choice := [
  ⟨1707,967,9,14,[0,6,4,2,3,1,5,8,10,9,7,12,13,11]⟩,
  ⟨7583,4027,13,14,[7,8,9,10,11,12,13,0,1,2,3,4,5,6]⟩,
  ⟨7997,4027,13,14,[1,2,5,4,3,0,6,13,9,8,7,11,10,12]⟩,
  ⟨6071,4027,13,14,[7,9,11,13,8,10,12,1,3,5,0,2,4,6]⟩,
  ⟨6826,967,9,14,[10,7,11,8,12,9,13,0,4,1,5,2,6,3]⟩,
  ⟨4027,4027,13,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩]
private def lookuprank8127 : List ℕ := [0,2,0,3,0,1,0,2,0,1,4,0,0,0,2,0,0,2,0,1,0,2,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,2,0,0,0,1,0,2,0,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,2,0,1,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,1,0,1,0,0,1,0,0,0,4,2,0,3,0,1,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,4,3,4,1,0,2,4,1,4,3,5,0,2,0,2,2,2,1,0,2,2,1,2,2,2,0,4,2,0,3,0,1,0,2,0,1,4,0,0,0,3,2,3,0,3,1,0,2,3,1,3,3,3,0,4,2,0,3,0,1,0,2,0,1,4,0,0,0,1,1,1,1,1,0,0,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,2,1,0,0,2,1,2,2,2,0,4,2,0,3,0,1,0,2,0,1,4,0,0,0,1,1,1,1,1,1,0,1,1,0,1,1,1,0,4,2,4,3,4,1,0,2,4,1,0,3,5,0,3,2,0,3,0,1,0,2,0,1,3,0,0,0,5,2,0,3,0,1,0,2,0,1,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank8127 : Floor 8127 16 := by
  apply certified choicesrank8127 lookuprank8127
  · intro r hr
    simp only [choicesrank8127,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank4027 (by decide +kernel)
    · exact floorMono rank4027 (by decide +kernel)
    · exact floorMono rank4027 (by decide +kernel)
    · exact floorMono rank967 (by decide +kernel)
    · exact floorMono rank4027 (by decide +kernel)
  · have good : choicesrank8127.all (fun r => decide (Verified 8127 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank8191 : List Choice := [
  ⟨4091,4091,15,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨6127,4091,15,14,[0,1,4,3,2,6,5,7,10,9,8,12,11,13]⟩,
  ⟨7677,4091,15,14,[0,2,1,6,4,5,3,8,7,12,10,11,9,13]⟩,
  ⟨6910,2031,13,14,[4,5,3,0,2,1,6,10,11,9,13,8,7,12]⟩,
  ⟨8061,4091,15,14,[1,2,3,4,5,6,0,13,7,8,9,10,11,12]⟩,
  ⟨8127,8127,16,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨8159,8127,16,14,[0,1,4,3,2,6,5,7,10,9,8,12,11,13]⟩,
  ⟨8183,8127,16,14,[0,2,1,6,4,5,3,8,7,12,10,11,9,13]⟩]
private def lookuprank8191 : List ℕ := [0,2,0,3,1,3,3,3,3,2,3,1,0,0,2,0,0,2,1,2,2,2,2,2,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,2,0,0,1,6,5,4,3,2,3,1,0,0,1,1,0,1,0,1,1,1,1,1,1,1,0,0,3,2,0,6,1,0,5,4,3,2,3,1,0,0,3,2,0,5,1,5,0,4,3,2,3,1,0,0,3,2,0,4,1,4,4,0,3,2,3,1,0,0,3,2,0,3,1,3,3,3,0,2,3,1,0,0,2,2,0,2,1,2,2,2,2,0,2,1,0,0,3,2,0,3,1,3,3,3,3,2,0,1,0,0,1,1,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,7,1,6,5,4,3,2,3,1,0,0,2,0,0,2,1,2,2,2,2,2,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,2,0,0,1,6,5,4,7,2,7,1,0,0,1,1,0,1,0,1,1,1,1,1,1,1,0,0,6,2,0,6,1,0,5,4,6,2,6,1,0,0,5,2,0,5,1,5,0,4,5,2,5,1,0,0,4,2,0,4,1,4,4,0,4,2,4,1,0,0,3,2,0,7,1,6,5,4,0,2,3,1,0,0,2,2,0,2,1,2,2,2,2,0,2,1,0,0,3,2,0,7,1,6,5,4,3,2,0,1,0,0,1,1,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank8191 : Floor 8191 18 := by
  apply certified choicesrank8191 lookuprank8191
  · intro r hr
    simp only [choicesrank8191,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank4091 (by decide +kernel)
    · exact floorMono rank4091 (by decide +kernel)
    · exact floorMono rank4091 (by decide +kernel)
    · exact floorMono rank2031 (by decide +kernel)
    · exact floorMono rank4091 (by decide +kernel)
    · exact floorMono rank8127 (by decide +kernel)
    · exact floorMono rank8127 (by decide +kernel)
    · exact floorMono rank8127 (by decide +kernel)
  · have good : choicesrank8191.all (fun r => decide (Verified 8191 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesrank16383 : List Choice := [
  ⟨4091,4091,15,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨13295,4091,15,14,[1,0,6,3,2,4,5,7,9,10,13,12,11,8]⟩,
  ⟨15551,4091,15,14,[1,3,4,0,6,5,2,7,13,12,9,8,10,11]⟩,
  ⟨16255,8191,18,14,[1,2,3,4,5,6,0,13,7,8,9,10,11,12]⟩,
  ⟨16351,8191,18,14,[7,8,11,10,9,13,12,0,3,2,1,5,4,6]⟩,
  ⟨16375,8191,18,14,[7,9,8,13,11,12,10,1,0,5,3,4,2,6]⟩,
  ⟨16381,8191,18,14,[7,13,10,9,11,12,8,1,0,2,3,6,5,4]⟩,
  ⟨16382,8191,18,14,[13,7,12,9,11,10,8,1,2,0,4,6,5,3]⟩,
  ⟨8191,8191,18,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨12287,8191,18,14,[0,3,2,1,5,4,6,7,8,11,10,9,13,12]⟩,
  ⟨16379,8191,18,14,[7,8,13,10,12,11,9,0,1,6,3,5,4,2]⟩,
  ⟨14335,8191,18,14,[0,3,6,1,4,5,2,7,8,12,10,13,9,11]⟩,
  ⟨15359,8191,18,14,[1,0,5,3,4,2,6,7,9,8,13,11,12,10]⟩,
  ⟨16367,8191,18,14,[7,8,12,10,13,9,11,0,3,6,1,4,5,2]⟩]
private def lookuprank16383 : List ℕ := [0,6,0,5,1,4,2,3,2,2,1,1,0,0,6,0,0,5,1,4,2,3,2,2,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,1,4,2,3,2,2,1,1,0,0,1,1,0,1,0,1,1,1,1,1,1,1,0,0,4,4,0,4,1,0,2,3,2,2,1,1,0,0,2,2,0,2,1,2,0,2,2,2,1,1,0,0,3,3,0,3,1,3,2,0,2,2,1,1,0,0,2,2,0,2,1,2,2,2,0,2,1,1,0,0,2,2,0,2,1,2,2,2,2,0,1,1,0,0,1,1,0,1,1,1,1,1,1,1,0,1,0,0,1,1,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,7,5,7,4,7,3,7,7,7,7,7,7,6,0,6,5,6,4,6,3,6,6,6,6,6,6,7,6,0,5,10,4,10,3,10,10,10,10,0,0,5,5,5,0,5,4,5,3,5,5,5,5,5,5,7,6,10,5,0,4,13,3,13,13,1,1,9,8,4,4,4,4,4,0,4,3,4,4,4,4,4,4,7,6,10,5,13,4,0,3,2,2,12,11,9,8,3,3,3,3,3,3,3,0,3,3,3,3,3,3,7,6,10,5,13,4,2,3,0,2,12,11,9,8,7,6,10,5,13,4,2,3,2,0,12,11,9,8,7,6,10,5,1,4,12,3,12,12,0,1,9,8,7,6,10,5,1,4,11,3,11,11,1,0,9,8,7,6,0,5,9,4,9,3,9,9,9,9,0,0,7,6,0,5,8,4,8,3,8,8,8,8,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rank16383 : Floor 16383 20 := by
  apply certified choicesrank16383 lookuprank16383
  · intro r hr
    simp only [choicesrank16383,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono rank4091 (by decide +kernel)
    · exact floorMono rank4091 (by decide +kernel)
    · exact floorMono rank4091 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
    · exact floorMono rank8191 (by decide +kernel)
  · have good : choicesrank16383.all (fun r => decide (Verified 16383 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

#print axioms rank8127
#print axioms rank8191
#print axioms rank16383
end Checkpoint132.Induced
