import ProjectedBoundary
import ScreenProof

namespace Checkpoint129.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Heawood
open Checkpoint125.Certificate Checkpoint126.Heawood Checkpoint127.Heawood Checkpoint128.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def ValidScreen (c : Screen) : Prop :=
  21+c.matching.length+(endpoints (decoded c.shape.mask)).card+c.cap≥
    26+(vertices c.shape.domain).card+(decoded c.shape.mask).card ∧ c.matching.Nodup ∧
  (∀ i∈c.matching, i∉decoded c.shape.mask) ∧
  (∀ i∈c.matching,∀ j∈c.matching,i≠j → Disjoint (ends i) (ends j)) ∧
  c.positives.headD 0 ∈ c.positives ∧
  (∀ n∈c.positives,∃ i : Fin 21,i∈decoded c.shape.mask ∧ ∀ v : V,sample c.shape n v=positive i v) ∧
  (∀ n∈c.negatives,¬predicate (sample c.shape n)) ∧
  0∉c.signals ∧ (∀ v : V,v∉vertices c.shape.domain → wordOf c.shape {v}=0) ∧
  (∀ v : V,wordOf c.shape {v}∈0::c.signals) ∧
  ∀ v : V,∀ s∈(liveNbr c v).sublists, wordOf c.shape s.toFinset∈0::c.signals
instance (c) : Decidable (ValidScreen c) := by
  unfold ValidScreen
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

private theorem regular {w c} (hc : ValidScreen c) (eq : lost w=decoded c.shape.mask)
    (hs : survivors w⊆G.edgeFinset) {s} (h : Regular (survivors w) s) : wordOf c.shape s∈0::c.signals := by
  obtain ⟨_,_,_,_,_,_,_,_,_,singles,larger⟩ := hc
  rcases h with tiny|⟨v,adj⟩
  · by_cases live : s.Nonempty
    · obtain ⟨u,hu⟩ := live
      have same : s={u} := eq_singleton_iff_unique_mem.mpr ⟨hu,fun _ ha => card_le_one.mp tiny _ ha _ hu⟩
      exact same ▸ singles u
    · have same := not_nonempty_iff_eq_empty.mp live
      have off : wordOf c.shape ∅=0 := rfl
      simp [same,off]
  · let l := (liveNbr c v).filter (fun u => decide (u∈s))
    have hl := larger v l (List.mem_sublists.mpr (List.filter_sublist ..))
    have same : l.toFinset=s := by
      ext u
      simp only [l,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
      intro hu
      have keep := adj u hu
      have edge : G.Adj v u := by simpa using hs keep
      refine List.mem_filter.mpr ⟨edge,decide_eq_true ?_⟩
      rw [←eq,lostEdges]
      exact fun conflict => (mem_sdiff.mp conflict).2 keep
    exact same ▸ hl

/-- For a verified row table, an arbitrary short correct Heawood circuit with
the specified lost edges gives a correct circuit within the projected gate cap. -/
theorem projectedScreenNecessary (gs : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) {c : Screen} (hc : ValidScreen c)
    (eq : lost ((run 14 gs).wires.getD out default)=decoded c.shape.mask) :
    ∃ book : List (Binary.Tree {m : ℕ // m∈c.signals}), ∃ t, Binary.Built book ∧ Binary.Ready book t ∧
      book.length≤c.cap ∧
      (∀ n∈c.positives,t.eval (fun m => (m.val &&& n)!=0)) ∧
      (∀ n∈c.negatives,¬t.eval (fun m => (m.val &&& n)!=0)) := by
  classical
  let w := (run 14 gs).wires.getD out default
  have valid := port (run_valid 14 gs).1 out
  have sound (z) (hz : accepts w z) := (spec z).mp (valid.sound z hz)
  have hs : survivors w⊆G.edgeFinset := (budget (run_valid 14 gs).1 out spec).sub
  obtain ⟨cap,nd,live,apart,nonempty,on,off,zero,outside,_,_⟩ := id hc
  have mj := jobsOfMatching sound c.matching nd apart (fun i hi => by
    by_contra gone
    exact live i hi (eq ▸ (show i∈lost w from mem_filter.mpr ⟨mem_univ _,gone⟩)))
  have total : G.edgeFinset.card=21 := by decide +kernel
  have ls : missed w=(decoded c.shape.mask).card := by rw [←lostSize,eq]
  rw [missed,card_sdiff_of_subset hs,total] at ls
  have hx := card_le_card hs
  rw [total] at hx
  let R := {n : ℕ // n∈c.positives ∨ n∈c.negatives}
  let rows (r : R) := sample c.shape r.val
  have yes {n} (hn : n∈c.positives) : ∃ i∈lost w,sample c.shape n=positive i := by
    obtain ⟨i,hi,same⟩ := on n hn
    exact ⟨i,eq ▸ hi,funext same⟩
  have positiveRow {n} (hn : n∈c.positives) : predicate (sample c.shape n) := by
    obtain ⟨i,_,same⟩ := yes hn
    rw [same]; exact positiveYes i
  have bd (r : R) : BoundaryRow w (rows r) := r.property.elim (fun h => Or.inl (yes h)) (fun h => Or.inr (off _ h))
  let f (s : Support 14) : Option {m : ℕ // m∈c.signals} :=
    if h : wordOf c.shape s∈c.signals then some ⟨wordOf c.shape s,h⟩ else none
  let signal (r : R) (m : {m : ℕ // m∈c.signals}) : Prop := (m.val &&& r.val)!=0
  have agree (r : R) (s : Support 14) (reg : Regular (survivors w) s) :
      (f s).elim False (signal r) ↔ lit s (rows r) := by
    by_cases ok : wordOf c.shape s∈c.signals
    · simpa [f,signal,rows,ok] using wordOn c.shape s r.val
    · have zero := (List.mem_cons.mp (regular hc eq hs reg)).resolve_right ok
      have no : ¬lit s (rows r) := by rw [←wordOn,zero]; simp
      simp [f,ok,no]
  have dead (v : V) (hv : v∉vertices c.shape.domain) : f {v}=none := by simp [f,outside v hv,zero]
  obtain ⟨book,t,ok,ready,truth,bound⟩ := projectedBoundaryCircuit gs out spec rows
    ⟨⟨_,Or.inl nonempty⟩,positiveRow nonempty⟩ bd (vertices c.shape.domain) f dead signal agree
  change (survivors w).card+(endpoints (lost w)).card+w.jobs.card+book.length≤gs.length+(vertices c.shape.domain).card at bound
  rw [eq] at bound
  exact ⟨book,t,ok,ready,by omega,fun n hn => (truth ⟨n,Or.inl hn⟩).mpr (positiveRow hn),
    fun n hn good => off n hn ((truth ⟨n,Or.inr hn⟩).mp good)⟩

#print axioms projectedScreenNecessary
end Checkpoint129.Heawood
