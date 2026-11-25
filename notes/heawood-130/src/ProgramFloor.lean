import KernelFloor
import FifteenScreens
import PostedModel

namespace Checkpoint130.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Prune
open PEqualNP.Outside.L_meta_3004_aux.Controls

private def vertexPort : Label→Value V
  | .inr _ => .bit false
  | .inl s => if h : s.Nonempty then .wire (s.min' h) else .bit false

/-- The project's instruction list, including its false default for unavailable
wires, supplies a vertex-labeled binary gate library of at most the same size. -/
theorem vertexProgram (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) :
    ∃ book : List (Binary.Tree V), ∃ e, Binary.Built book ∧ Binary.Ready book e ∧
      book.length≤ops.length ∧ ∀ z : V→Bool,e.eval (fun v => z v=true) ↔ predicate z := by
  classical
  let s := run 14 ops
  obtain ⟨gs,e,hb,hr,faith,count⟩ := circuitBook ∅ ∅ ops out
  have budget : gs.length≤ops.length := by
    have spentAll := (run_valid 14 ops).2
    have w : waste ∅ s.bottom ≤ s.bottom.length := List.length_filter_le ..
    change gs.length=spent ∅ ∅ s at count
    simp [spent,extra] at count
    change Checkpoint122.Pruning.cost s=ops.length at spentAll
    unfold Checkpoint122.Pruning.cost at spentAll
    omega
  have same (z : V→Bool) (a) (ha : a∈e.vars) :
      (vertexPort a).truth (fun v => z v=true) ↔ interpret z a := by
    cases a with
    | inr u => simp [vertexPort,Value.truth,interpret]
    | inl S =>
      by_cases live : S.Nonempty
      · have only : S.card≤1 := (faith.regular S ha).elim id (fun ⟨_,all⟩ => by
          obtain ⟨v,hv⟩ := live
          simpa using all v hv)
        have minMem := S.min'_mem live
        simp only [vertexPort,dite_eq_left live,Value.truth,interpret,lit]
        constructor
        · exact fun h => ⟨_,minMem,h⟩
        · exact fun ⟨v,hv,on⟩ => (card_le_one.mp only _ hv _ minMem) ▸ on
      · simp [vertexPort,Value.truth,interpret,lit,not_nonempty_iff_eq_empty.mp live]
  have truth (z : V→Bool) : (specialize vertexPort e).truth (fun t => t.eval (fun v => z v=true)) ↔ predicate z := by
    rw [semantics]
    exact (Iff.intro (e.mono (fun a ha => (same z a ha).mp)) (e.mono (fun a ha => (same z a ha).mpr))).trans
      ((faith.exactOn z (by simp [Domain])).trans (spec z))
  cases he : specialize vertexPort e with
  | bit b =>
    have yes := (truth (positive 0)).mpr (positiveYes 0)
    have empty : ¬predicate (fun _ => false) := by decide +kernel
    have no := fun h => empty ((truth _).mp h)
    simp only [he,Value.truth] at yes no
    exact False.elim (no yes)
  | wire t =>
    have live : reduce vertexPort e=some t := by simp [reduce,he,Value.port]
    obtain ⟨ok,go⟩ := library vertexPort hb
    have price := Checkpoint130.Prune.cost vertexPort hb hr live
    exact ⟨_,t,ok,go e hr t live,by omega,fun z => by simpa [he,Value.truth] using truth z⟩

theorem programNineteen (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) : 19≤ops.length := by
  obtain ⟨gs,e,hb,hr,cap,truth⟩ := vertexProgram ops out spec
  exact (nineteen hb hr truth).trans cap

theorem programTwentyTwo (localFloor : ∀ gs : List (Binary.Tree Port), ∀ t,
    Binary.Built gs → Binary.Ready gs t → Fits valPos valNeg t → 16≤gs.length)
    (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z) : 22≤ops.length := by
  obtain ⟨gs,e,hb,hr,cap,truth⟩ := vertexProgram ops out spec
  exact (twentyTwo localFloor hb hr truth).trans cap

theorem postedNineteen (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (h : Checkpoint122.Posted.Witness i f g tail) : 17≤tail.length := by
  let qs := Checkpoint122.Posted.codes i f g tail
  have bound := programNineteen (qs.map Checkpoint122.Posted.decode) (13+qs.length)
    (Checkpoint122.Posted.semantics _ h.2)
  simp only [List.length_map,qs,Checkpoint122.Posted.codes,List.length_cons] at bound
  omega

theorem postedTwentyTwo (localFloor : ∀ gs : List (Binary.Tree Port), ∀ t,
    Binary.Built gs → Binary.Ready gs t → Fits valPos valNeg t → 16≤gs.length)
    (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (h : Checkpoint122.Posted.Witness i f g tail) : 20≤tail.length := by
  let qs := Checkpoint122.Posted.codes i f g tail
  have bound := programTwentyTwo localFloor (qs.map Checkpoint122.Posted.decode) (13+qs.length)
    (Checkpoint122.Posted.semantics _ h.2)
  simp only [List.length_map,qs,Checkpoint122.Posted.codes,List.length_cons] at bound
  omega

/-- All five selected fifteen-loss representatives admit their displayed local
budget whenever the posted circuit is correct and uses at most 26 gates. -/
theorem fifteenNecessary (ops : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 ops).wires.getD out default).full z=true ↔ predicate z)
    (short : ops.length≤26) {c : Checkpoint128.Heawood.Screen} (listed : c∈fifteen)
    (eq : lost ((run 14 ops).wires.getD out default)=Checkpoint127.Heawood.decoded c.shape.mask) :
    ∃ book : List (Binary.Tree {m : ℕ // m∈c.signals}), ∃ t, Binary.Built book ∧ Binary.Ready book t ∧
      book.length≤c.cap ∧
      (∀ n∈c.positives,t.eval (fun m => (m.val &&& n)!=0)) ∧
      (∀ n∈c.negatives,¬t.eval (fun m => (m.val &&& n)!=0)) :=
  Checkpoint129.Heawood.projectedScreenNecessary ops out spec short (fifteenValid listed) eq

#print axioms postedTwentyTwo
#print axioms fifteenNecessary
#print axioms vertexProgram
#print axioms programNineteen
#print axioms programTwentyTwo
#print axioms postedNineteen
end Checkpoint130.Heawood
