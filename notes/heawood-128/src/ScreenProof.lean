import ElevenSamples

namespace Checkpoint128.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Heawood
open Checkpoint125.Certificate Checkpoint127.Heawood PEqualNP.Outside.L_meta_3004_aux.Controls

def liveNbr (c : Screen) (v : V) := (nbr v).filter
  (fun u => decide (s(v,u)∉(decoded c.shape.mask).image edge))

private def Info (c : Screen) : Prop :=
  (decoded c.shape.mask).card=11 ∧ 10+c.matching.length+c.cap=26 ∧ c.matching.Nodup ∧
  (∀ i∈c.matching, i∉decoded c.shape.mask) ∧
  (∀ i∈c.matching,∀ j∈c.matching,i≠j → Disjoint (ends i) (ends j)) ∧
  c.positives.headD 0 ∈ c.positives ∧
  (∀ n∈c.positives,∃ i : Fin 21,i∈decoded c.shape.mask ∧ ∀ v : V,sample c.shape n v=positive i v) ∧
  (∀ n∈c.negatives,¬predicate (sample c.shape n)) ∧
  (∀ v : V,wordOf c.shape {v}∈0::c.signals) ∧
  ∀ v : V,∀ s∈(liveNbr c v).sublists, wordOf c.shape s.toFinset∈0::c.signals
private instance (c) : Decidable (Info c) := by
  unfold Info
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem checked {c} (hc : c∈screens) : Info c := by
  have all : screens.all (fun c => decide (Info c))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ hc)

private theorem regular {w c} (hc : c∈screens) (eq : lost w=decoded c.shape.mask)
    (hs : survivors w⊆G.edgeFinset) {s} (h : Regular (survivors w) s) : wordOf c.shape s∈0::c.signals := by
  obtain ⟨_,_,_,_,_,_,_,_,singles,larger⟩ := checked hc
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

/-- Each of the seven sampled eleven-loss representatives must pass its
recorded gate cap, including those with surviving edges between sampled vertices. -/
theorem screenNecessary (gs : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) {c : Screen} (hc : c∈screens)
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
  obtain ⟨size,cap,nd,live,apart,nonempty,on,off,_,_⟩ := checked hc
  have mj := jobsOfMatching sound c.matching nd apart (fun i hi => by
    by_contra gone
    exact live i hi (eq ▸ (show i∈lost w from mem_filter.mpr ⟨mem_univ _,gone⟩)))
  have total : G.edgeFinset.card=21 := by decide +kernel
  have ls : missed w=11 := by rw [←lostSize,eq,size]
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
  obtain ⟨book,t,ok,ready,truth,bound⟩ := boundaryCircuit gs out spec rows
    ⟨⟨_,Or.inl nonempty⟩,positiveRow nonempty⟩ bd f signal agree
  change (survivors w).card+w.jobs.card+book.length≤gs.length at bound
  exact ⟨book,t,ok,ready,by omega,fun n hn => (truth ⟨n,Or.inl hn⟩).mpr (positiveRow hn),
    fun n hn good => off n hn ((truth ⟨n,Or.inr hn⟩).mp good)⟩

#print axioms screenNecessary
end Checkpoint128.Heawood
