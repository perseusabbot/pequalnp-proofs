import ResidualForms

namespace Checkpoint124.Shapes

private def safe (limit : ℕ) (q : Frame) := !q.cut || q.pool.all (fun f => decide (f.length≤limit))

/-- Traverse continuations depth first so the checker only retains the current branch. -/
private def scan (limit : ℕ) : ℕ → ℕ → Frame → Bool
  | 0, _, q => safe limit q
  | d+1, k, q => (next k q).all (scan limit d (k+1))

private theorem transfer {limit} (d k)
    (h : ∀ q∈frames k, scan limit d k q=true) :
    ∀ q∈frames (k+d), safe limit q=true := by
  induction d generalizing k with
  | zero => exact h
  | succ d ih =>
    have step : ∀ q∈frames (k+1), scan limit d (k+1) q=true := by
      intro q hq
      obtain ⟨p,hp,mem⟩ := List.mem_flatMap.mp hq
      exact List.all_eq_true.mp (h p hp) q mem
    simpa only [Nat.add_assoc, Nat.add_comm 1 d] using ih (k+1) step

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem early : scan 0 0 0 start && scan 0 1 0 start &&
    scan 1 2 0 start && scan 2 3 0 start = true := by decide +kernel

/-- Splitting after two gates keeps every finite check within a small kernel budget. -/
private def branch (i : ℕ) := scan 4 2 2 ((frames 2).getD i start)

private theorem branch0 : branch 0=true := by decide +kernel
private theorem branch1 : branch 1=true := by decide +kernel
private theorem branch2 : branch 2=true := by decide +kernel
private theorem branch3 : branch 3=true := by decide +kernel
private theorem branch4 : branch 4=true := by decide +kernel
private theorem branch5 : branch 5=true := by decide +kernel
private theorem branch6 : branch 6=true := by decide +kernel
private theorem branch7 : branch 7=true := by decide +kernel
private theorem branch8 : branch 8=true := by decide +kernel
private theorem branch9 : branch 9=true := by decide +kernel
private theorem branch10 : branch 10=true := by decide +kernel
private theorem branch11 : branch 11=true := by decide +kernel
private theorem branch12 : branch 12=true := by decide +kernel
private theorem branch13 : branch 13=true := by decide +kernel
private theorem branch14 : branch 14=true := by decide +kernel
private theorem branch15 : branch 15=true := by decide +kernel
private theorem branch16 : branch 16=true := by decide +kernel
private theorem branch17 : branch 17=true := by decide +kernel
private theorem branch18 : branch 18=true := by decide +kernel
private theorem branch19 : branch 19=true := by decide +kernel
private theorem branch20 : branch 20=true := by decide +kernel
private theorem branch21 : branch 21=true := by decide +kernel
private theorem branch22 : branch 22=true := by decide +kernel
private theorem branch23 : branch 23=true := by decide +kernel
private theorem branch24 : branch 24=true := by decide +kernel
private theorem branch25 : branch 25=true := by decide +kernel
private theorem branch26 : branch 26=true := by decide +kernel
private theorem branch27 : branch 27=true := by decide +kernel
private theorem branch28 : branch 28=true := by decide +kernel
private theorem branch29 : branch 29=true := by decide +kernel
private theorem branch30 : branch 30=true := by decide +kernel
private theorem branch31 : branch 31=true := by decide +kernel
private theorem branch32 : branch 32=true := by decide +kernel
private theorem branch33 : branch 33=true := by decide +kernel
private theorem branch34 : branch 34=true := by decide +kernel
private theorem branch35 : branch 35=true := by decide +kernel
private theorem branch36 : branch 36=true := by decide +kernel
private theorem branch37 : branch 37=true := by decide +kernel
private theorem branch38 : branch 38=true := by decide +kernel
private theorem branch39 : branch 39=true := by decide +kernel
private theorem branch40 : branch 40=true := by decide +kernel
private theorem branch41 : branch 41=true := by decide +kernel
private theorem branch42 : branch 42=true := by decide +kernel
private theorem branch43 : branch 43=true := by decide +kernel
private theorem branch44 : branch 44=true := by decide +kernel
private theorem branch45 : branch 45=true := by decide +kernel
private theorem branch46 : branch 46=true := by decide +kernel
private theorem branch47 : branch 47=true := by decide +kernel
private theorem branch48 : branch 48=true := by decide +kernel


private theorem four (q) (h : q∈frames 4) : safe 4 q=true := by
  refine transfer 2 2 ?_ q h
  intro p hp
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  have len : (frames 2).length=49 := by decide +kernel
  have bound : i<49 := len ▸ hi
  rw [←eq,←List.getD_eq_getElem _ start hi]
  change branch i=true
  interval_cases i
  · exact branch0
  · exact branch1
  · exact branch2
  · exact branch3
  · exact branch4
  · exact branch5
  · exact branch6
  · exact branch7
  · exact branch8
  · exact branch9
  · exact branch10
  · exact branch11
  · exact branch12
  · exact branch13
  · exact branch14
  · exact branch15
  · exact branch16
  · exact branch17
  · exact branch18
  · exact branch19
  · exact branch20
  · exact branch21
  · exact branch22
  · exact branch23
  · exact branch24
  · exact branch25
  · exact branch26
  · exact branch27
  · exact branch28
  · exact branch29
  · exact branch30
  · exact branch31
  · exact branch32
  · exact branch33
  · exact branch34
  · exact branch35
  · exact branch36
  · exact branch37
  · exact branch38
  · exact branch39
  · exact branch40
  · exact branch41
  · exact branch42
  · exact branch43
  · exact branch44
  · exact branch45
  · exact branch46
  · exact branch47
  · exact branch48

theorem lengthBound {k q f} (small : k≤4) (hq : q∈frames k) (cut : q.cut=true)
    (mem : f∈q.pool) : f.length≤cap k := by
  have e := early
  simp only [Bool.and_eq_true] at e
  have lift (n m) (h : scan m n 0 start=true) : ∀ p∈frames n, safe m p=true := by
    simpa using transfer (limit:=m) n 0 (fun p hp => by obtain rfl := List.mem_singleton.mp hp; exact h)
  have checked : safe (cap k) q=true := by
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 by omega) with rfl|rfl|rfl|rfl|rfl
    · exact lift 0 0 e.1.1.1 _ hq
    · exact lift 1 0 e.1.1.2 _ hq
    · exact lift 2 1 e.1.2 _ hq
    · exact lift 3 2 e.2 _ hq
    · exact four q hq
  simp only [safe,cut,Bool.not_true,Bool.false_or,List.all_eq_true,decide_eq_true_eq] at checked
  exact checked f mem

#print axioms lengthBound
end Checkpoint124.Shapes
