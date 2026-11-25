import CoreGeometry

namespace Checkpoint126.Heawood
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Contract Checkpoint125.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def supportOf : Label → Support 14
  | .inl S => S
  | .inr _ => ∅

private def labelCode (p : Chain) (t : Label) := Binary.primitive (decide (token p.b=t)) (decide (token p.c=t))
  (decide (p.a∈supportOf t ∨ p.d∈supportOf t))

private theorem outerBit : ∀ (a h : Bool) (i : Fin 4),
    Binary.bit (Binary.primitive false false a) h i=true ↔ h=true ∧ a=true := by decide +kernel

private theorem sameCode (p : Chain) (v : V) : labelCode p (token v)=code p (token v) := by
  simp [labelCode,Checkpoint125.Heawood.code,supportOf,token]

private theorem outside (p : Chain) (h : Bool) (i : Fin 4) (v : V) (b : p.b≠v) (c : p.c≠v) :
    input p h i v=true ↔ h=true ∧ (p.a=v ∨ p.d=v) := by
  simpa [input,Checkpoint125.Heawood.code,token,b,c] using outerBit (decide (p.a=v ∨ p.d=v)) h i

private theorem plain (p : Chain) (h : Bool) (i : Fin 4) (S : Support 14) (b : p.b∉S) (c : p.c∉S) :
    Binary.bit (labelCode p (.inl S)) h i=true ↔ interpret (input p h i) (.inl S) := by
  have ne (u : V) (miss : u∉S) : token u≠Sum.inl S := by
    intro e
    have eq : {u}=S := Sum.inl.inj e
    exact miss (eq ▸ mem_singleton_self u)
  have left : Binary.bit (labelCode p (.inl S)) h i=true ↔ h=true ∧ (p.a∈S ∨ p.d∈S) := by
    simp only [labelCode,supportOf,ne _ b,ne _ c,decide_false,outerBit]
    exact and_congr_right' ⟨of_decide_eq_true,decide_eq_true⟩
  rw [left]
  change _ ↔ ∃ v∈S,input p h i v=true
  have agrees (v : V) (hv : v∈S) := outside p h i v (fun eq => b (eq ▸ hv)) (fun eq => c (eq ▸ hv))
  constructor
  · rintro ⟨on,ha|hd⟩
    · exact ⟨p.a,ha,(agrees _ ha).mpr ⟨on,Or.inl rfl⟩⟩
    · exact ⟨p.d,hd,(agrees _ hd).mpr ⟨on,Or.inr rfl⟩⟩
  · rintro ⟨v,hv,yes⟩
    obtain ⟨on,eq|eq⟩ := (agrees _ hv).mp yes
    · exact ⟨on,Or.inl (eq ▸ hv)⟩
    · exact ⟨on,Or.inr (eq ▸ hv)⟩

private theorem literal (p : Chain) (h : Bool) (i : Fin 4) (v : V) :
    Binary.bit (labelCode p (token v)) h i=true ↔ interpret (input p h i) (token v) := by
  rw [sameCode]
  change input p h i v=true ↔ lit {v} (input p h i)
  simp [lit]

private theorem product (p : Chain) (h : Bool) (i : Fin 4) (t : Product 14) :
    Binary.bit (labelCode p (.inr t)) h i=true ↔ interpret (input p h i) (.inr t) := by
  cases h <;> simp [labelCode,supportOf,token,Binary.primitive,Binary.bit,interpret]

/-- A single additional regular input to a read-once expression cannot realize
the restriction on every three-edge path in the missing cycle. -/
theorem auxiliaryPath {q} (hq : q∈cores) {w : Wire 14} (sub : (Checkpoint125.Certificate.interior q.1).toFinset⊆lost w)
    (spec : ∀ z, w.full z=true ↔ predicate z) (sound : ∀ z, accepts w z → predicate z) (hs : survivors w⊆G.edgeFinset)
    {e : Expr} (faith : Faithful (survivors w) w.jobs w e) (extra : Label) (ex : extra∈e.vars)
    (leaves : e.vars⊆insert extra (forced w)) (once : e.inputs.Nodup) : False := by
  have reg : Regular (survivors w) (supportOf extra) := by
    cases extra with
    | inl S => exact faith.regular S ex
    | inr _ => exact Or.inl (by simp [supportOf])
  obtain ⟨p,hp,within,good⟩ := safePath hq sub (supportOf extra) reg hs
  obtain ⟨truth,selected,_⟩ := of_decide_eq_true (List.all_eq_true.mp pathsChecked p hp)
  have sig := Binary.signatureBound (token p.b) (token p.c) (labelCode p) e once
    (fun t _ => Binary.primitiveOK ..)
  apply Binary.recover sig
  intro h i
  let z := input p h i
  have dom : Domain w.jobs z := domain sound sub (fun v hv => within v (selected h i v hv))
  have matchLeaf (t : Label) (ht : t∈e.vars) : Binary.bit (labelCode p t) h i=true ↔ interpret z t := by
    rcases mem_insert.mp (leaves ht) with rfl|forcedLeaf
    · cases t with
      | inr t => exact product p h i t
      | inl S =>
        change S.card≤1 ∨ (p.b∉S ∧ p.c∉S) at good
        rcases good with small|⟨b,c⟩
        · by_cases nonempty : S.Nonempty
          · obtain ⟨v,hv⟩ := nonempty
            have eq : S={v} := eq_singleton_iff_unique_mem.mpr ⟨hv,fun x hx => card_le_one.mp small _ hx _ hv⟩
            subst S
            exact literal p h i v
          · have eq := not_nonempty_iff_eq_empty.mp nonempty
            subst S
            exact plain p h i _ (by simp) (by simp)
        · exact plain p h i S b c
    · rcases mem_union.mp forcedLeaf with lit|prod
      · obtain ⟨v,_,rfl⟩ := mem_image.mp lit
        exact literal p h i v
      · obtain ⟨u,_,rfl⟩ := mem_image.mp prod
        exact product p h i u
  have ev : e.eval (fun t => Binary.bit (labelCode p t) h i=true) ↔ e.eval (interpret z) :=
    ⟨e.mono (fun t ht => (matchLeaf t ht).mp),e.mono (fun t ht => (matchLeaf t ht).mpr)⟩
  exact Bool.eq_iff_iff.mpr ((Binary.bitTruth ..).trans (ev.trans
    ((faith.exactOn z dom).trans ((spec z).trans (truth h i)))))

#print axioms auxiliaryPath
end Checkpoint126.Heawood
