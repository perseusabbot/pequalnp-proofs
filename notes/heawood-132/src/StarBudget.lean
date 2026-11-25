import RetainedCost

namespace Checkpoint132.Star
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Heawood
open Checkpoint125.Certificate Checkpoint126.Heawood Checkpoint127.Heawood Checkpoint128.Heawood Checkpoint129.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def star : Screen :=
  ⟨⟨262143,16319,[1,2,4,8,16,32,0,128,256,512,1024,2048,4096,8192]⟩,22,[18],[1,2,4,8,16,32,128,256,512,768,1024,2048,2304,2560,2816,4096,8192],[129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128],[63,180,314,432,541,660,792,1038,1290,1548,2087,2212,2338,2565,3078,3716,4115,4370,4625,5008,6147,7426,8233,8488,8713,9992,10273,10656,14849,16256]⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem starValid : ValidScreen star := by decide +kernel

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


def RowFloor (c : Screen) (k : ℕ) : Prop :=
  ∀ gs : List (Binary.Tree {m : ℕ // m∈c.signals}), ∀ e, Binary.Built gs → Binary.Ready gs e →
    (∀ n∈c.positives,e.eval (fun a => (a.val &&& n)!=0)) →
    (∀ n∈c.negatives,¬e.eval (fun a => (a.val &&& n)!=0)) → k≤gs.length

theorem screenCost {c : Screen} {k : ℕ} (hc : ValidScreen c) (lower : RowFloor c k)
    (gs : List Op) (out : ℕ) (spec : ∀ z,((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (eq : lost ((run 14 gs).wires.getD out default)=decoded c.shape.mask) :
    let s := run 14 gs
    let w := s.wires.getD out default
    (kept (survivors w) s.bottom).length+2*w.jobs.card+k≤gs.length := by
  classical
  let w := (run 14 gs).wires.getD out default
  have valid := port (run_valid 14 gs).1 out
  have sound (z) (hz : accepts w z) := (spec z).mp (valid.sound z hz)
  have hs : survivors w⊆G.edgeFinset := (budget (run_valid 14 gs).1 out spec).sub
  obtain ⟨_,_,_,_,nonempty,on,off,_,_,_,_⟩ := id hc
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
  obtain ⟨book,t,ok,ready,truth,pay⟩ := Checkpoint132.Retained.projectedCost gs out spec rows
    ⟨⟨_,Or.inl nonempty⟩,positiveRow nonempty⟩ bd f signal agree
  have bound := lower book t ok ready (fun n hn => (truth ⟨n,Or.inl hn⟩).mpr (positiveRow hn))
    (fun n hn good => off n hn ((truth ⟨n,Or.inr hn⟩).mp good))
  omega

/-- Equality at the 26-gate budget fixes the number of retained bottom gates and
leaves just one distinct product, whose rectangle covers all three surviving edges. -/
theorem starEquality (lower : RowFloor star 22) (gs : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (eq : lost ((run 14 gs).wires.getD out default)=decoded star.shape.mask) (short : gs.length≤26) :
    let s := run 14 gs
    let w := s.wires.getD out default
    gs.length=26 ∧ (kept (survivors w) s.bottom).length=2 ∧
      ∃ p,w.jobs={p} ∧ survivors w=part p := by
  classical
  let s := run 14 gs
  let w := s.wires.getD out default
  let H := survivors w
  have valid : Valid s := (run_valid 14 gs).1
  have bw := budget valid out spec
  have sound (z) (hz : accepts w z) := (spec z).mp ((port valid out).sound z hz)
  have total : G.edgeFinset.card=21 := by decide +kernel
  have lostCount : (decoded star.shape.mask).card=18 := by decide +kernel
  have loss : missed w=18 := by rw [←lostSize,eq,lostCount]
  rw [missed,card_sdiff_of_subset bw.sub,total] at loss
  change 21-H.card=18 at loss
  have hs : H.card=3 := by omega
  have c := bw.cubic
  change H.card≤3*w.jobs.card at c
  have bottom := chargedBottom (w:=w) s.bottom valid.bottom
    (fun p h => valid.operands p ((port valid out).owned p h)) sound
  have split := List.length_eq_countP_add_countP (l:=s.bottom) (fun a => decide (Regular H a))
  simp only [List.countP_eq_length_filter] at split
  change s.bottom.length=(kept H s.bottom).length+waste H s.bottom at split
  change H.card+waste H s.bottom≤w.jobs.card+s.bottom.length at bottom
  have price := screenCost starValid lower gs out spec eq
  change (kept H s.bottom).length+2*w.jobs.card+22≤gs.length at price
  have jobs : w.jobs.card=1 := by omega
  obtain ⟨p,hp⟩ := card_eq_one.mp jobs
  exact ⟨by omega,by change (kept H s.bottom).length=2; omega,p,hp,by change w.jobs.biUnion part=part p; rw [hp]; simp⟩

#print axioms starValid
#print axioms screenCost
#print axioms starEquality
end Checkpoint132.Star
