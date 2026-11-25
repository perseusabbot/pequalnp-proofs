import SmallChecks
import CherryBound

namespace Checkpoint127.Small
open Finset Checkpoint125 Checkpoint126.Cherry
private def label {k} (t : Option (Slot k)) := t.map Subtype.val

private theorem member {k} (t : Option (Slot k)) : label t∈terminals k := by
  cases t with
  | none => simp [label,terminals]
  | some v => simp [label,terminals,v.property]

private theorem need {k} {c : Case} {p : ℕ × Row × Row} (sep : Separates k c p)
    (e : Binary.Tree (Option (Slot k)))
    (truth : ∀ r, e.eval (fun t => seen c (label t) r=true) ↔ target k r=true) :
    some p.1∈e.vars.image label := by
  let v : Slot k := ⟨p.1,sep.1⟩
  have hv : some v∈e.vars := by
    by_contra miss
    have no := sep.2.2.1
    have on := (truth p.2.1).mpr sep.2.1
    have off := (truth p.2.2).mp (e.mono (fun t ht ht' => by
      cases t with
      | none => exact sep.2.2.2.1 ht'
      | some s =>
        apply sep.2.2.2.2 s.val s.property _ ht'
        intro same
        exact miss ((show s=v from Subtype.ext same) ▸ ht)) on)
    simp [no] at off
  exact mem_image.mpr ⟨some v,hv,rfl⟩

private theorem noSwitch {k} {c : Case} (sw : Switch k c) (e : Binary.Tree (Option (Slot k)))
    (once : e.inputs.Nodup) (truth : ∀ r,e.eval (fun t => seen c (label t) r=true) ↔ target k r=true) : False := by
  let x : Option (Slot k) := some ⟨c.first,sw.1⟩
  let y : Option (Slot k) := some ⟨c.second,sw.2.1⟩
  let sig := fun t : Option (Slot k) => signature c (label t)
  have inj : Function.Injective (label (k:=k)) := by
    rintro (_|a) (_|b) h <;> simp_all [label,Subtype.ext_iff]
  have legal (t : Option (Slot k)) : sig t∈Binary.catalog (decide (x=t)) (decide (y=t)) := by
    have h := (sw.2.2.1 _ (member t)).1
    change sig t∈Binary.catalog (decide (label x=label t)) (decide (label y=label t)) at h
    simpa only [inj.eq_iff] using h
  apply Binary.recover (Binary.signatureBound x y sig e once (fun t _ => legal t))
  intro h i
  have bits (t : Option (Slot k)) := (sw.2.2.1 _ (member t)).2 h i
  apply Bool.eq_iff_iff.mpr
  rw [Binary.bitTruth]
  change e.eval (fun t => Binary.bit (signature c (label t)) h i=true) ↔ Binary.bit (8,14) h i=true
  simp_rw [bits]
  rw [truth,sw.2.2.2]

/-- Either small graph needs at least eight binary gates, with wire sharing.
For the subdivided claw, every disjunction of its three tips is free. -/
theorem lower {k} {book : List (Binary.Tree (Slot k))} (built : Binary.Built book)
    {e : Binary.Tree (Slot k)} (ready : Binary.Ready book e)
    (truth : ∀ r,e.eval (fun v => signal v.val r=true) ↔ target k r=true) : 8≤book.length := by
  classical
  generalize hn : book.length=n
  induction n using Nat.strong_induction_on generalizing book e with
  | ind n ih =>
    rcases bottom e with ⟨v,rfl⟩|⟨op,x,y,occurs⟩
    · obtain ⟨r,diff⟩ := (checked k).1 v.val v.property
      exact False.elim (diff (Bool.eq_iff_iff.mpr (truth r)))
    · let g : Binary.Tree (Slot k) := .gate op (.leaf x) (.leaf y)
      have used : g∈book := listed built e ready g occurs
      by_cases eq : x=y
      · subst y
        obtain ⟨ok,go⟩ := covered g id x built
        have len := oneLess id x used
        have ev (r) : (cut g id x e).eval (fun v => signal v.val r=true) ↔ target k r=true := by
          have same : (signal x.val r=true) ↔ g.eval (fun v => signal (id v).val r=true) := by
            cases op <;> simp [g,Binary.Tree.eval]
          exact (cutTruth g id x _ same e).trans (truth r)
        exact (ih _ (by omega) ok (go _ ready) ev rfl).trans (by omega)
      · obtain ⟨c,hc,mat⟩ := (checked k).2.1 x.val x.property y.val y.property op (fun same => eq (Subtype.ext same))
        have good := (checked k).2.2 c hc
        let f : Slot k→Option (Slot k) := some
        let t := cut g f none e
        obtain ⟨ok,go⟩ := covered g f none built
        have cap := Binary.inputBudget ok (go e ready)
        change t.vars.card≤(upper g f none book).length+1 ∧
          (t.vars.card=(upper g f none book).length+1 → t.inputs.Nodup) at cap
        have freshNode : none∈t.vars := fresh f none e occurs
        have len := oneLess f none used
        have ev (r) : t.eval (fun u => seen c (label u) r=true) ↔ target k r=true := by
          let ρ := fun u : Option (Slot k) => seen c (label u) r=true
          have same : ρ none ↔ g.eval (fun a => ρ (f a)) := by
            rcases mat.2 with ⟨hx,hy⟩|⟨hx,hy⟩ <;> cases hop : op <;>
              simp [g,Binary.Tree.eval,ρ,seen,label,gate,mat.1,hop,hx,hy,f,and_comm,or_comm]
          exact (cutTruth g f none ρ same e).trans (truth r)
        let M := (c.needed.map Prod.fst).toFinset
        have lifted : M.image some⊆t.vars.image label := by
          rintro _ h
          obtain ⟨u,hu,rfl⟩ := mem_image.mp h
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
          exact need (good.2.2.1 p hp) t ev
        have inc := card_le_card (insert_subset (mem_image_of_mem label freshNode) lifted)
        change (insert none (M.image some)).card≤(t.vars.image label).card at inc
        have size : (insert none (M.image some)).card=c.needed.length+1 := by
          simp [M,card_image_of_injective _ (Option.some_injective ℕ),List.toFinset_card_of_nodup good.1]
        rw [size] at inc
        have low := inc.trans (card_image_le (s:=t.vars) (f:=label))
        have six := good.2.1
        by_contra! small
        rcases good.2.2.2 with seven|sw
        · omega
        · exact noSwitch sw t (cap.2 (by omega)) ev

#print axioms lower
end Checkpoint127.Small
