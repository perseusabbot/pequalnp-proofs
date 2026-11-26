import FixedPool

namespace Checkpoint134
open Finset
open PEqualNP.Outside.L_meta_9338 (V Box hit legal bit)

def spin (b : Box) : Box := (univ.filter (fun i : V => i+7∈b.1),univ.filter (fun j : V => j+7∈b.2))
@[simp] theorem spinRow (b : Box) (i : V) : i∈(spin b).1 ↔ i+7∈b.1 := by simp [spin]
@[simp] theorem spinCol (b : Box) (j : V) : j∈(spin b).2 ↔ j+7∈b.2 := by simp [spin]
theorem period (b : Box) : spin (spin (spin b))=b := by
  have e : ∀ v : V,v+7+7+7=v := by decide +kernel
  apply Prod.ext <;> ext v <;> simp only [spinRow,spinCol,e]
def orbit (b : Box) : Finset Box := {b,spin b,spin (spin b)}
theorem orbitHit (b c : Box) (hc : c∈orbit b) {i j : V} (h : hit c i j) : Hit b i j := by
  simp only [orbit,mem_insert,mem_singleton] at hc
  rcases hc with rfl|rfl|rfl
  · exact ⟨0,by simpa [step,hit] using h⟩
  · exact ⟨1,by simpa [step,hit] using h⟩
  · have e : ∀ v : V,v+step 2=v+7+7 := by decide +kernel
    exact ⟨2,by simpa only [e,hit,spinRow,spinCol] using h⟩
theorem insideOrbit (b : Box) {w : Box} : spin w∈orbit b ↔ w∈orbit b := by
  simp only [orbit,mem_insert,mem_singleton]
  constructor
  · rintro (e|e|e)
    · exact Or.inr (Or.inr (by simpa only [period] using congrArg (fun x => spin (spin x)) e))
    · exact Or.inl (by simpa only [period] using congrArg (fun x => spin (spin x)) e)
    · exact Or.inr (Or.inl (by simpa only [period] using congrArg (fun x => spin (spin x)) e))
  · rintro (rfl|rfl|rfl) <;> simp [period]
theorem orbitCard (b : Box) :
    (orbit b).card = if spin b=b then 1 else 3 := by
  by_cases h : spin b=b
  · simp [orbit,h]
  · have n : spin (spin b)≠b := fun e => h (by simpa only [period] using (congrArg spin e).symm)
    have m : spin (spin b) ≠ spin b := fun e => h (by simpa only [period] using congrArg (fun x => spin (spin x)) e)
    have reverse : b≠spin b := Ne.symm h
    simp [orbit,h,reverse,Ne.symm n,Ne.symm m,Finset.card_insert_of_notMem]
def stable (s : Finset Box) := ∀ b∈s,spin b∈s
def covers (s : Finset Box) := ∀ i j,bit i j=false → ∃ b∈s,hit b i j

theorem decompose (s : Finset Box) (closed : stable s) :
    ∃ fs ms : List Box, fs.length+3*ms.length=s.card ∧
      (∀ b∈fs,b∈s ∧ spin b=b) ∧ (∀ b∈ms,b∈s) ∧
      ∀ b∈s,b∈fs ∨ ∃ c∈ms,b∈orbit c := by
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases empty : s=∅
  · subst s; exact ⟨[],[],by simp,by simp,by simp,by simp⟩
  obtain ⟨b,hb⟩ := nonempty_iff_ne_empty.mpr empty
  let t := s \ orbit b
  have sub : orbit b ⊆ s := by
    intro x h
    simp only [orbit,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl
    · exact hb
    · exact closed _ hb
    · exact closed _ (closed _ hb)
  have ot : b∈orbit b := by simp [orbit]
  have small : t ⊂ s := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨sdiff_subset,?_⟩
    intro e
    have m : b∈t := e ▸ hb
    exact (mem_sdiff.mp m).2 ot
  have inh : stable t := by
    intro w hw
    exact mem_sdiff.mpr ⟨closed _ (mem_sdiff.mp hw).1,fun h => (mem_sdiff.mp hw).2 ((insideOrbit b).mp h)⟩
  obtain ⟨fs,ms,n,fix,mov,cov⟩ := ih t small inh
  have count := card_sdiff_add_card_eq_card sub
  change t.card+(orbit b).card=s.card at count
  have fx : ∀w∈fs,w∈s ∧ spin w=w := fun w hw => ⟨(mem_sdiff.mp (fix w hw).1).1,(fix w hw).2⟩
  have mv : ∀w∈ms,w∈s := fun w hw => (mem_sdiff.mp (mov w hw)).1
  by_cases f : spin b=b
  · rw [orbitCard,if_pos f] at count
    refine ⟨b::fs,ms,by simp only [List.length_cons]; omega,?_,mv,?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|h
      · exact ⟨hb,f⟩
      · exact fx _ h
    · intro w hw
      by_cases eq : w=b
      · exact Or.inl (List.mem_cons.mpr (Or.inl eq))
      · have ht : w∈t := mem_sdiff.mpr ⟨hw,by simpa [orbit,f] using eq⟩
        exact (cov w ht).imp (List.mem_cons_of_mem b) id
  · rw [orbitCard,if_neg f] at count
    refine ⟨fs,b::ms,by simp only [List.length_cons]; omega,fx,?_,?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|h
      · exact hb
      · exact mv _ h
    · intro w hw
      by_cases ino : w∈orbit b
      · exact Or.inr ⟨b,List.mem_cons_self,ino⟩
      · rcases cov w (mem_sdiff.mpr ⟨hw,ino⟩) with h|⟨a,ha,h⟩
        · exact Or.inl h
        · exact Or.inr ⟨a,List.mem_cons_of_mem _ ha,h⟩

def residue (p : V) : Row := ⟨p.val%7,Nat.mod_lt _ (by decide)⟩
def safe (p q : Row) := ([22,44,88,49,98,69,11] : List ℕ)[p.val]!.testBit q.val
def rowStar (p : Row) : FixedPool.Index := ([0,1,2,3,5,7,10] : List FixedPool.Index)[p.val]!
def colStar (p : Row) : FixedPool.Index := ([13,12,8,11,4,6,9] : List FixedPool.Index)[p.val]!
theorem fixedContains (b : Box) (g : legal b) (fixed : spin b=b) :
    ∃ k : FixedPool.Index,∀p q,hit b p q → FixedPool.contains k p q := by
  have row (p : V) : p+7∈b.1 ↔ p∈b.1 := by rw [←spinRow,fixed]
  have col (q : V) : q+7∈b.2 ↔ q∈b.2 := by rw [←spinCol,fixed]
  have phase (p : V) : p+step 2=p+7+7 := (by decide +kernel : ∀v : V,v+step 2=v+7+7) p
  have e : ∀ p q : V,(∀ u v : Phase,bit (p+step u) (q+step v)=false) → safe (residue p) (residue q)=true := by decide +kernel
  have ok (p q : V) (hp : p∈b.1) (hq : q∈b.2) : safe (residue p) (residue q)=true := by
    apply e
    intro u v
    apply g
    · fin_cases u
      · simpa [step] using hp
      · exact (row _).mpr hp
      · change p+step 2 ∈ _
        rw [phase,row,row]
        exact hp
    · fin_cases v
      · simpa [step] using hq
      · exact (col _).mpr hq
      · change q+step 2 ∈ _
        rw [phase,col,col]
        exact hq
  have stars : ∀p q, safe (residue p) (residue q)=true →
      FixedPool.contains (rowStar (residue p)) p q ∧ FixedPool.contains (colStar (residue q)) p q := by decide +kernel
  have unique : ∀ a a' c c' : Row,safe a c=true → safe a c'=true → safe a' c=true → safe a' c'=true → a=a' ∨ c=c' := by decide +kernel
  by_cases rows : b.1.Nonempty
  · obtain ⟨a,ha⟩ := rows
    by_cases same : ∀p∈b.1,residue p=residue a
    · refine ⟨rowStar (residue a),fun p q h => ?_⟩
      rw [←same p h.1]
      exact (stars p q (ok _ _ h.1 h.2)).1
    · push Not at same
      obtain ⟨a',ha',diff⟩ := same
      by_cases cols : b.2.Nonempty
      · obtain ⟨c,hc⟩ := cols
        refine ⟨colStar (residue c),fun p q h => ?_⟩
        have eq := (unique _ _ _ _ (ok _ _ ha' h.2) (ok _ _ ha' hc)
          (ok _ _ ha h.2) (ok _ _ ha hc)).resolve_left diff
        rw [←eq]
        exact (stars p q (ok _ _ h.1 h.2)).2
      · exact ⟨0,fun _ q h => False.elim (cols ⟨q,h.2⟩)⟩
  · exact ⟨0,fun p _ h => False.elim (rows ⟨p,h.1⟩)⟩

#print axioms decompose
#print axioms fixedContains
end Checkpoint134
