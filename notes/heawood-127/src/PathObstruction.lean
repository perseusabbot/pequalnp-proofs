import ReadOnce
import TerminalBudget

namespace Checkpoint125.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125.Contract
open PEqualNP.Outside.L_meta_3004_aux.Controls

structure Chain where
  a : V
  b : V
  c : V
  d : V
  deriving DecidableEq

def paths : List Chain := do
  let a ← List.finRange 14
  let b ← nbr a
  let c ← (nbr b).filter (·!=a)
  let d ← (nbr c).filter (fun d => d != a && d != b)
  return ⟨a,b,c,d⟩

def link (a b : V) := Fin.ofNat 21 (edges.idxOf (min a.val b.val,max a.val b.val))
def Chain.links (p : Chain) := [link p.a p.b,link p.b p.c,link p.c p.d]
def Chain.vertices (p : Chain) := [p.a,p.b,p.c,p.d]
def token (v : V) : Label := .inl {v}
def code (p : Chain) (t : Label) := Binary.primitive (decide (token p.b=t)) (decide (token p.c=t))
  (decide (token p.a=t ∨ token p.d=t))
def input (p : Chain) (h : Bool) (i : Fin 4) (v : V) := Binary.bit (code p (token v)) h i

def PathTruth (p : Chain) : Prop :=
  (∀ (h : Bool) (i : Fin 4), predicate (input p h i) ↔ Binary.bit (8,14) h i=true) ∧
  (∀ (h : Bool) (i : Fin 4) (v : V), input p h i v=true → v∈p.vertices) ∧
  (∀ u∈p.vertices, ∀ v∈p.vertices, G.Adj u v → ∃ j∈p.links, edge j=s(u,v))
private instance (p) : Decidable (PathTruth p) := by
  unfold PathTruth
  exact @instDecidableAnd _ _ (by infer_instance)
    (@instDecidableAnd _ _ (by infer_instance) (by infer_instance))
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem pathsChecked : paths.all (fun p => decide (PathTruth p))=true := by
  decide +kernel

def ContainsPath (L : Finset (Fin 21)) := ∃ p∈paths, ∀ j∈p.links, j∈L

private theorem obstruction {w : Wire 14} (spec : ∀ z, w.full z=true ↔ predicate z)
    (sound : ∀ z, accepts w z → predicate z) {e : Expr} (faith : Faithful (survivors w) w.jobs w e)
    (leaves : e.vars=forced w) (once : e.inputs.Nodup) (present : ContainsPath (lost w)) : False := by
  obtain ⟨p,hp,inside⟩ := present
  obtain ⟨truth,selected,edgesOK⟩ := of_decide_eq_true (List.all_eq_true.mp pathsChecked p hp)
  have sig := Binary.signatureBound (token p.b) (token p.c) (code p) e once
    (fun t _ => Binary.primitiveOK ..)
  apply Binary.recover sig
  intro h i
  let z := input p h i
  have domain : Domain w.jobs z := by
    rintro q hq ⟨⟨u,hu,zu⟩,v,hv,zv⟩
    have live := (in_survivors w _).mpr ⟨q,hq,u,hu,v,hv,rfl⟩
    have adj := (describe sound).2 q hq u hu v hv
    obtain ⟨j,hj,eq⟩ := edgesOK u (selected h i u zu) v (selected h i v zv) adj
    exact (mem_filter.mp (inside j hj)).2 (eq ▸ live)
  have matchLeaf (t : Label) (ht : t∈e.vars) :
      Binary.bit (code p t) h i=true ↔ interpret z t := by
    rw [leaves] at ht
    rcases mem_union.mp ht with literal|product
    · obtain ⟨v,_,rfl⟩ := mem_image.mp literal
      change z v=true ↔ lit {v} z
      simp [lit]
    · obtain ⟨q,_,rfl⟩ := mem_image.mp product
      cases h <;> simp [code,Binary.primitive,Binary.bit,token,interpret]
  have ev : e.eval (fun t => Binary.bit (code p t) h i=true) ↔ e.eval (interpret z) :=
    ⟨e.mono (fun t ht => (matchLeaf t ht).mp),e.mono (fun t ht => (matchLeaf t ht).mpr)⟩
  exact Bool.eq_iff_iff.mpr ((Binary.bitTruth ..).trans (ev.trans
    ((faith.exactOn z domain).trans ((spec z).trans (truth h i)))))

/-- Three consecutive lost edges force another gate. The outer inputs switch
the predicate on the middle inputs from AND to OR. -/
theorem pathBudget (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (path : ContainsPath (lost ((run 14 gs).wires.getD out default))) :
    let w := (run 14 gs).wires.getD out default
    (survivors w).card+(endpoints (lost w)).card+w.jobs.card ≤ gs.length := by
  let w := (run 14 gs).wires.getD out default
  obtain ⟨bound,eqCase⟩ := terminalBudget gs out spec
  change (survivors w).card+(endpoints (lost w)).card+w.jobs.card ≤ gs.length+1 at bound
  change (survivors w).card+(endpoints (lost w)).card+w.jobs.card ≤ gs.length
  by_contra! big
  have eq : (survivors w).card+(endpoints (lost w)).card+w.jobs.card=gs.length+1 := by omega
  obtain ⟨e,fa,leaves,once⟩ := eqCase eq
  have fw := port (run_valid 14 gs).1 out
  exact obstruction spec (fun z hz => (spec z).mp (fw.sound z hz)) fa leaves once path

#print axioms pathBudget
end Checkpoint125.Heawood
