import SeedRanks0

namespace Checkpoint132.Induced

private def choicesseed4091 : List Choice := [
  ⟨2019,2019,12,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨3545,2019,12,14,[0,3,2,1,5,4,6,7,8,11,10,9,13,12]⟩,
  ⟨3771,3771,13,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨3034,1963,11,14,[12,9,11,10,8,13,7,5,3,1,2,0,4,6]⟩,
  ⟨3953,2019,12,14,[1,2,3,4,5,6,0,13,7,8,9,10,11,12]⟩]
private def lookupseed4091 : List ℕ := [0,1,0,0,0,1,2,3,2,1,3,0,0,0,1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,1,1,1,0,0,0,2,1,0,0,0,1,0,2,2,1,2,0,0,0,3,1,0,0,0,1,2,0,2,1,3,0,0,0,2,1,0,0,0,1,2,2,0,1,2,0,0,0,1,1,0,0,0,1,1,1,1,0,1,0,0,0,3,1,0,0,0,1,2,3,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,2,4,2,1,3,0,0,0,1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,1,1,1,0,0,0,2,1,0,0,0,1,0,2,2,1,2,0,0,0,4,1,0,0,0,1,2,0,2,1,4,0,0,0,2,1,0,0,0,1,2,2,0,1,2,0,0,0,1,1,0,0,0,1,1,1,1,0,1,0,0,0,3,1,0,0,0,1,2,4,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem seed4091 (checks : SeedChecks) : Floor 4091 16 := by
  apply certified choicesseed4091 lookupseed4091
  · intro r hr
    simp only [choicesseed4091,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact floorMono (seed2019 checks) (by decide +kernel)
    · exact floorMono (seed2019 checks) (by decide +kernel)
    · exact floorMono (seed3771 checks) (by decide +kernel)
    · exact floorMono (seed1963 checks) (by decide +kernel)
    · exact floorMono (seed2019 checks) (by decide +kernel)
  · have good : choicesseed4091.all (fun r => decide (Verified 4091 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesseed8127 : List Choice := [
  ⟨5549,2019,12,14,[0,3,6,1,4,5,2,7,8,12,10,13,9,11]⟩,
  ⟨3771,3771,13,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨7866,3771,13,14,[13,9,8,7,11,10,12,1,2,5,4,3,0,6]⟩,
  ⟨5007,1959,11,14,[7,8,9,10,11,12,13,0,1,2,3,4,5,6]⟩,
  ⟨6055,3771,13,14,[7,9,11,13,8,10,12,1,3,5,0,2,4,6]⟩,
  ⟨7485,3771,13,14,[1,2,5,4,3,0,6,13,9,8,7,11,10,12]⟩]
private def lookupseed8127 : List ℕ := [0,0,1,2,0,2,0,2,1,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,2,0,1,0,0,3,0,4,1,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,3,0,0,0,3,1,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,4,0,3,0,0,1,0,3,0,1,0,1,0,1,1,0,1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,3,0,3,0,3,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,0,2,0,2,1,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,2,0,1,0,0,4,0,4,1,0,4,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,4,0,0,0,5,1,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,4,0,5,0,0,1,0,5,0,1,0,1,0,1,1,0,1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,4,0,3,0,5,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem seed8127 (checks : SeedChecks) : Floor 8127 17 := by
  apply certified choicesseed8127 lookupseed8127
  · intro r hr
    simp only [choicesseed8127,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono (seed2019 checks) (by decide +kernel)
    · exact floorMono (seed3771 checks) (by decide +kernel)
    · exact floorMono (seed3771 checks) (by decide +kernel)
    · exact floorMono (seed1959 checks) (by decide +kernel)
    · exact floorMono (seed3771 checks) (by decide +kernel)
    · exact floorMono (seed3771 checks) (by decide +kernel)
  · have good : choicesseed8127.all (fun r => decide (Verified 8127 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesseed8191 : List Choice := [
  ⟨2019,2019,12,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨7677,4091,16,14,[0,2,1,6,4,5,3,8,7,12,10,11,9,13]⟩,
  ⟨6890,2019,12,14,[13,7,12,9,11,10,8,1,2,0,4,6,5,3]⟩,
  ⟨8061,4091,16,14,[1,2,3,4,5,6,0,13,7,8,9,10,11,12]⟩,
  ⟨8127,8127,17,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨8159,8127,17,14,[0,1,4,3,2,6,5,7,10,9,8,12,11,13]⟩,
  ⟨4051,3771,13,12,[7,9,8,13,11,12,10,1,0,5,3,4,2,6]⟩,
  ⟨6055,3771,13,11,[7,9,11,13,8,10,12,1,3,5,0,2,4,6]⟩,
  ⟨8183,8127,17,14,[0,2,1,6,4,5,3,8,7,12,10,11,9,13]⟩]
private def lookupseed8191 : List ℕ := [0,1,0,0,0,2,2,2,2,1,2,0,0,0,1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,0,0,0,4,3,2,1,2,0,0,0,2,1,0,0,0,4,0,3,2,1,2,0,0,0,2,1,0,0,0,3,3,0,2,1,2,0,0,0,2,1,0,0,0,2,2,2,0,1,2,0,0,0,1,1,0,0,0,1,1,1,1,0,1,0,0,0,2,1,0,0,0,2,2,2,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,8,2,5,4,3,2,1,2,7,6,0,1,0,1,1,1,1,1,1,1,1,1,1,1,0,2,1,0,0,0,5,4,3,2,1,2,0,0,0,8,1,0,0,0,5,4,3,8,1,8,0,0,0,2,1,0,0,0,5,4,3,2,1,2,0,0,0,5,1,5,5,5,0,4,3,5,1,5,5,5,0,4,1,4,4,4,4,0,3,4,1,4,4,4,0,3,1,3,3,3,3,3,0,3,1,3,3,3,0,2,1,2,8,2,5,4,3,0,1,2,7,6,0,1,1,1,1,1,1,1,1,1,0,1,1,1,0,2,1,2,8,2,5,4,3,2,1,0,7,6,0,7,1,0,0,0,5,4,3,7,1,7,0,0,0,6,1,0,0,0,5,4,3,6,1,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem seed8191 (checks : SeedChecks) : Floor 8191 19 := by
  apply certified choicesseed8191 lookupseed8191
  · intro r hr
    simp only [choicesseed8191,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono (seed2019 checks) (by decide +kernel)
    · exact floorMono (seed4091 checks) (by decide +kernel)
    · exact floorMono (seed2019 checks) (by decide +kernel)
    · exact floorMono (seed4091 checks) (by decide +kernel)
    · exact floorMono (seed8127 checks) (by decide +kernel)
    · exact floorMono (seed8127 checks) (by decide +kernel)
    · exact floorMono (seed3771 checks) (by decide +kernel)
    · exact floorMono (seed3771 checks) (by decide +kernel)
    · exact floorMono (seed8127 checks) (by decide +kernel)
  · have good : choicesseed8191.all (fun r => decide (Verified 8191 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

private def choicesseed16383 : List Choice := [
  ⟨4091,4091,16,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨13295,4091,16,14,[1,0,6,3,2,4,5,7,9,10,13,12,11,8]⟩,
  ⟨15551,4091,16,14,[1,3,4,0,6,5,2,7,13,12,9,8,10,11]⟩,
  ⟨16255,8191,19,14,[1,2,3,4,5,6,0,13,7,8,9,10,11,12]⟩,
  ⟨16351,8191,19,14,[7,8,11,10,9,13,12,0,3,2,1,5,4,6]⟩,
  ⟨16375,8191,19,14,[7,9,8,13,11,12,10,1,0,5,3,4,2,6]⟩,
  ⟨16381,8191,19,14,[7,13,10,9,11,12,8,1,0,2,3,6,5,4]⟩,
  ⟨16382,8191,19,14,[13,7,12,9,11,10,8,1,2,0,4,6,5,3]⟩,
  ⟨8191,8191,19,14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩,
  ⟨12287,8191,19,14,[0,3,2,1,5,4,6,7,8,11,10,9,13,12]⟩,
  ⟨16379,8191,19,14,[7,8,13,10,12,11,9,0,1,6,3,5,4,2]⟩,
  ⟨14335,8191,19,14,[0,3,6,1,4,5,2,7,8,12,10,13,9,11]⟩,
  ⟨15359,8191,19,14,[1,0,5,3,4,2,6,7,9,8,13,11,12,10]⟩,
  ⟨16367,8191,19,14,[7,8,12,10,13,9,11,0,3,6,1,4,5,2]⟩]
private def lookupseed16383 : List ℕ := [0,6,0,5,1,4,2,3,2,2,1,1,0,0,6,0,0,5,1,4,2,3,2,2,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,1,4,2,3,2,2,1,1,0,0,1,1,0,1,0,1,1,1,1,1,1,1,0,0,4,4,0,4,1,0,2,3,2,2,1,1,0,0,2,2,0,2,1,2,0,2,2,2,1,1,0,0,3,3,0,3,1,3,2,0,2,2,1,1,0,0,2,2,0,2,1,2,2,2,0,2,1,1,0,0,2,2,0,2,1,2,2,2,2,0,1,1,0,0,1,1,0,1,1,1,1,1,1,1,0,1,0,0,1,1,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,7,5,7,4,7,3,7,7,7,7,7,7,6,0,6,5,6,4,6,3,6,6,6,6,6,6,7,6,0,5,10,4,10,3,10,10,10,10,0,0,5,5,5,0,5,4,5,3,5,5,5,5,5,5,7,6,10,5,0,4,13,3,13,13,1,1,9,8,4,4,4,4,4,0,4,3,4,4,4,4,4,4,7,6,10,5,13,4,0,3,2,2,12,11,9,8,3,3,3,3,3,3,3,0,3,3,3,3,3,3,7,6,10,5,13,4,2,3,0,2,12,11,9,8,7,6,10,5,13,4,2,3,2,0,12,11,9,8,7,6,10,5,1,4,12,3,12,12,0,1,9,8,7,6,10,5,1,4,11,3,11,11,1,0,9,8,7,6,0,5,9,4,9,3,9,9,9,9,0,0,7,6,0,5,8,4,8,3,8,8,8,8,0,0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem seed16383 (checks : SeedChecks) : Floor 16383 21 := by
  apply certified choicesseed16383 lookupseed16383
  · intro r hr
    simp only [choicesseed16383,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorMono (seed4091 checks) (by decide +kernel)
    · exact floorMono (seed4091 checks) (by decide +kernel)
    · exact floorMono (seed4091 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
    · exact floorMono (seed8191 checks) (by decide +kernel)
  · have good : choicesseed16383.all (fun r => decide (Verified 16383 r))=true := by decide +kernel
    exact fun r h => of_decide_eq_true (List.all_eq_true.mp good r h)
  · decide +kernel

#print axioms seed4091
#print axioms seed8127
#print axioms seed8191
#print axioms seed16383
end Checkpoint132.Induced
