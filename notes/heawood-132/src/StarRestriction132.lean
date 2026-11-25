import StarShape

namespace Checkpoint132.Star
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Heawood
open Checkpoint125.Certificate Checkpoint127.Heawood Checkpoint128.Heawood Checkpoint129.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def singles : List ℕ := [1,2,4,8,16,32,128,256,512,1024,2048,4096,8192]
def limited (a : Support 14) := wordOf star.shape a :: 2816 :: singles

private theorem singleCode (S : Support 14) (h : S.card≤1) : wordOf star.shape S∈0::singles := by
  by_cases used : S.Nonempty
  · obtain ⟨v,hv⟩ := used
    have same : S={v} := eq_singleton_iff_unique_mem.mpr ⟨hv,fun _ ha => card_le_one.mp h _ ha _ hv⟩
    have checked : ∀ v : V,wordOf star.shape {v}∈0::singles := by decide +kernel
    exact same ▸ checked v
  · rw [not_nonempty_iff_eq_empty.mp used]
    exact List.mem_cons_self ..

/-- Only the pair actually built before the retained product and the triple itself
are free. The projected suffix has at most 22 binary gates. -/
theorem necessary (lower : RowFloor star 22) (gs : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (eq : lost ((run 14 gs).wires.getD out default)=decoded star.shape.mask) (short : gs.length≤26) :
    ∃ a : Support 14,a.card=2 ∧ a⊆tips ∧
    ∃ book : List (Binary.Tree {m : ℕ // m∈limited a}), ∃ e,Binary.Built book ∧ Binary.Ready book e ∧
      book.length≤22 ∧ (∀ n∈star.positives,e.eval (fun m => (m.val &&& n)!=0)) ∧
      (∀ n∈star.negatives,¬e.eval (fun m => (m.val &&& n)!=0)) := by
  classical
  let s := run 14 gs
  let w := s.wires.getD out default
  obtain ⟨size,j,⟨a,ac,sub,bank⟩⟩ := starGates lower gs out spec eq short
  change kept (survivors w) s.bottom=[tips,a] at bank
  change w.jobs={(center,tips)} ∨ w.jobs={(tips,center)} at j
  have jobs : w.jobs.card=1 := by rcases j with j|j <;> rw [j,card_singleton]
  obtain ⟨_,_,_,_,nonempty,on,off,_,_,_,_⟩ := starValid
  let R := {n : ℕ // n∈star.positives ∨ n∈star.negatives}
  let rows (r : R) := sample star.shape r.val
  have yes {n} (hn : n∈star.positives) : ∃ i∈lost w,sample star.shape n=positive i := by
    obtain ⟨i,hi,same⟩ := on n hn
    exact ⟨i,eq ▸ hi,funext same⟩
  have positiveRow {n} (hn : n∈star.positives) : predicate (sample star.shape n) := by
    obtain ⟨i,_,same⟩ := yes hn
    rw [same]; exact positiveYes i
  have bd (r : R) : BoundaryRow w (rows r) := r.property.elim (fun h => Or.inl (yes h)) (fun h => Or.inr (off _ h))
  let f (S : Support 14) : Option {m : ℕ // m∈limited a} :=
    if h : wordOf star.shape S∈limited a then some ⟨_,h⟩ else none
  let signal (r : R) (m : {m : ℕ // m∈limited a}) : Prop := (m.val &&& r.val)!=0
  have covered {S : Support 14} (h : S.card≤1 ∨ S∈kept (survivors w) s.bottom) :
      wordOf star.shape S∈0::limited a := by
    rw [bank] at h
    rcases h with tiny|mem
    · rcases List.mem_cons.mp (singleCode S tiny) with zero|lit
      · exact List.mem_cons.mpr (Or.inl zero)
      · simp [limited,lit]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl
      · have triple : wordOf star.shape tips=2816 := by decide +kernel
        simp [limited,triple]
      · simp [limited]
  have agree (r : R) (S : Support 14) (h : S.card≤1 ∨ S∈kept (survivors w) s.bottom) :
      (f S).elim False (signal r) ↔ lit S (rows r) := by
    by_cases pass : wordOf star.shape S∈limited a
    · simpa [f,signal,rows,pass] using wordOn star.shape S r.val
    · have zero := (List.mem_cons.mp (covered h)).resolve_right pass
      have no : ¬lit S (rows r) := by rw [←wordOn,zero]; simp
      simp [f,pass,no]
  obtain ⟨book,e,built,ready,truth,amount⟩ := Checkpoint132.Retained.projectedAvailable gs out spec rows
    ⟨⟨_,Or.inl nonempty⟩,positiveRow nonempty⟩ bd f signal agree
  change (kept (survivors w) s.bottom).length+2*w.jobs.card+book.length≤gs.length at amount
  rw [bank,jobs] at amount
  simp only [List.length_cons,List.length_nil] at amount
  exact ⟨a,ac,sub,book,e,built,ready,by omega,fun n hn => (truth ⟨n,Or.inl hn⟩).mpr (positiveRow hn),
    fun n hn good => off n hn ((truth ⟨n,Or.inr hn⟩).mp good)⟩

#print axioms necessary
end Checkpoint132.Star
