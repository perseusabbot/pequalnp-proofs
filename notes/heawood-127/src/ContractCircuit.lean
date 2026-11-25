import BinaryBudget
import RegularBottom

namespace Checkpoint125.Contract
open Finset Checkpoint122.Pruning Checkpoint124.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

abbrev Label := Sum (Support 14) (Product 14)
abbrev Expr := Binary.Tree Label
abbrev Graph := Finset (Sym2 V)

def interpret (z : V → Bool) : Label → Prop
  | .inl S => lit S z
  | .inr _ => False

def Domain (J : Finset (Product 14)) (z : V → Bool) := ∀ p∈J, ¬(lit p.1 z ∧ lit p.2 z)
def spent (H : Graph) (J : Finset (Product 14)) (s : State 14) :=
  waste H s.bottom+extra J s+s.dropped+s.top.length

structure Faithful (H : Graph) (J : Finset (Product 14)) (w : Wire 14) (e : Expr) : Prop where
  regular : ∀ S, Sum.inl S∈e.vars → Regular H S
  roots : ∀ p∈w.jobs, p∈J → Sum.inr p∈e.vars
  exactOn : ∀ z, Domain J z → (e.eval (interpret z) ↔ w.full z=true)

private theorem pureTruth {B T P d n} {w : Wire 14} (f : Fits B T P d n w) (hp : w.pure=true) (z) :
    lit w.raw z ↔ w.full z=true := by
  have eq : accepts w z ↔ lit w.raw z := by simp [accepts,Wire.jobs,f.empty hp]
  exact ⟨fun h => f.sound z (eq.mpr h),fun h => eq.mp (f.same (by simp [f.empty hp]) z h)⟩

private theorem joinFaith {H J a b e f} (x : Faithful H J a e) (y : Faithful H J b f) :
    Faithful H J (joinW a b) (.gate true e f) where
  regular := by
    intro S h
    rw [Binary.Tree.gateVars] at h
    exact (mem_union.mp h).elim (x.regular S) (y.regular S)
  roots := by
    intro p hp live
    change p∈(a.tags∪b.tags).eraseNone at hp
    rw [eraseNone_union] at hp
    rw [Binary.Tree.gateVars]
    exact (mem_union.mp hp).elim (fun h => mem_union_left _ (x.roots p h live))
      (fun h => mem_union_right _ (y.roots p h live))
  exactOn := by intro z hz; simp [Binary.Tree.eval,joinW,x.exactOn z hz,y.exactOn z hz]

private theorem andFaith {H J a b e f w} (x : Faithful H J a e) (y : Faithful H J b f)
    (empty : ∀ p∈w.jobs, p∉J) (full : ∀ z, w.full z=(a.full z && b.full z)) :
    Faithful H J w (.gate false e f) where
  regular := by
    intro S h
    rw [Binary.Tree.gateVars] at h
    exact (mem_union.mp h).elim (x.regular S) (y.regular S)
  roots := fun p hp live => False.elim (empty p hp live)
  exactOn := by intro z hz; simp [Binary.Tree.eval,full,x.exactOn z hz,y.exactOn z hz]

private def Has (H : Graph) (J : Finset (Product 14)) (book : List Expr) (w : Wire 14) :=
  ∃ e, Binary.Ready book e ∧ Faithful H J w e
private def Modeled (H : Graph) (J : Finset (Product 14)) (s : State 14) :=
  ∃ book, Binary.Built book ∧ book.length=spent H J s ∧ ∀ w∈s.wires, Has H J book w

private theorem portHas {H J book} {ws : List (Wire 14)} (h : ∀ w∈ws, Has H J book w) (i : ℕ) :
    Has H J book (ws.getD i default) := by
  by_cases good : i<ws.length
  · rw [List.getD_eq_getElem _ _ good]; exact h _ (List.getElem_mem ..)
  · rw [List.getD_eq_default _ _ (by omega)]
    refine ⟨.leaf (.inl ∅),Or.inl ⟨_,rfl⟩,?_⟩
    refine ⟨by simp [Regular],by simp [Wire.jobs,default,Inhabited.default],?_⟩
    intro z _
    simp [interpret,Binary.Tree.eval,lit,default,Inhabited.default]

private theorem keep {H J} {s : State 14} {book} (ok : Binary.Built book) (prior : ∀ w∈s.wires, Has H J book w)
    {t : State 14} {w : Wire 14} (wires : t.wires=s.wires++[w]) (cost : book.length=spent H J t)
    (fresh : Has H J book w) : Modeled H J t := by
  refine ⟨book,ok,cost,?_⟩
  rw [wires]
  intro u hu
  rcases List.mem_append.mp hu with h|h
  · exact prior _ h
  · exact List.mem_singleton.mp h ▸ fresh

private theorem pay {H J} {s : State 14} {book} (ok : Binary.Built book) (prior : ∀ w∈s.wires, Has H J book w)
    {t : State 14} {w : Wire 14} (wires : t.wires=s.wires++[w]) (cost : book.length+1=spent H J t)
    {a b : Expr} (ra : Binary.Ready book a) (rb : Binary.Ready book b)
    (op : Bool) (faith : Faithful H J w (.gate op a b)) : Modeled H J t := by
  let node := Binary.Tree.gate op a b
  refine ⟨node::book,⟨ok,op,a,b,rfl,ra,rb⟩,cost,?_⟩
  rw [wires]
  intro u hu
  rcases List.mem_append.mp hu with old|fresh
  · obtain ⟨e,ready,ev⟩ := prior u old
    exact ⟨e,ready.imp_right (List.mem_cons_of_mem _),ev⟩
  · obtain rfl := List.mem_singleton.mp fresh
    exact ⟨node,Or.inr (List.mem_cons_self ..),faith⟩

private theorem stepModel {H J s} (valid : Valid s) (g : Op) (model : Modeled H J s) : Modeled H J (step s g) := by
  obtain ⟨book,built,length,tracked⟩ := model
  let a := s.wires.getD g.left default
  let b := s.wires.getD g.right default
  have fa := port valid g.left
  have fb := port valid g.right
  obtain ⟨e,re,ea⟩ := portHas tracked g.left
  obtain ⟨f,rf,fbRep⟩ := portHas tracked g.right
  change Modeled H J (act s a b g.isOr)
  cases h : a.pure && b.pure with
  | true =>
    obtain ⟨ap,bp⟩ := Bool.and_eq_true_iff.mp h
    cases g.isOr with
    | true =>
      simp only [act,h]
      by_cases good : Regular H (a.raw∪b.raw)
      · refine keep built tracked rfl ?_ ⟨.leaf (.inl (a.raw∪b.raw)),Or.inl ⟨_,rfl⟩,?_⟩
        · simpa [spent,waste,extra,good] using length
        · have ta : a.tags=∅ := fa.empty ap
          have tb : b.tags=∅ := fb.empty bp
          refine ⟨by simpa using good,by simp [Wire.jobs,joinW,ta,tb],?_⟩
          intro z _
          change lit (a.raw∪b.raw) z ↔ (a.full z || b.full z)=true
          have both : lit (a.raw∪b.raw) z ↔ lit a.raw z ∨ lit b.raw z := by simp [lit,or_and_right,exists_or]
          rw [both,pureTruth fa ap,pureTruth fb bp,Bool.or_eq_true_iff]
      · refine pay built tracked rfl ?_ re rf true (joinFaith ea fbRep)
        rw [length]; simp [spent,waste,extra,good]; omega
    | false =>
      simp only [act,h]
      by_cases live : (a.raw,b.raw)∈J
      · refine keep built tracked rfl ?_ ⟨.leaf (.inr (a.raw,b.raw)),Or.inl ⟨_,rfl⟩,?_⟩
        · simpa [spent,extra,live] using length
        · refine ⟨by simp,by simp [meetW,Wire.jobs],?_⟩
          intro z domain
          change False ↔ (a.full z && b.full z)=true
          rw [Bool.and_eq_true_iff,←pureTruth fa ap,←pureTruth fb bp]
          exact ⟨False.elim,domain _ live⟩
      · refine pay built tracked rfl ?_ re rf false (andFaith ea fbRep (by simpa [meetW,Wire.jobs] using live) (fun _ => rfl))
        rw [length]; simp [spent,extra,live]; omega
  | false =>
    cases g.isOr with
    | true =>
      cases mix : a.pure || b.pure <;> simp only [act,h,mix,Bool.false_eq_true,ite_false,ite_true] <;>
        refine pay built tracked rfl ?_ re rf true (joinFaith ea fbRep) <;>
        rw [length] <;> simp [spent,extra] <;> omega
    | false =>
      simp only [act,h]
      refine pay built tracked rfl ?_ re rf false (andFaith ea fbRep (by simp [cutW,Wire.jobs]) (fun _ => rfl))
      rw [length]; simp [spent,extra]; omega

theorem circuitBook (H : Graph) (J : Finset (Product 14)) (gs : List Op) (out : ℕ) :
    let s := run 14 gs
    let w := s.wires.getD out default
    ∃ book : List Expr, ∃ e : Expr, Binary.Built book ∧ Binary.Ready book e ∧
      Faithful H J w e ∧ book.length=spent H J s := by
  have all (ops : List Op) : Modeled H J (run 14 ops) := by
    induction ops using List.reverseRecOn with
    | nil =>
      refine ⟨[],trivial,rfl,?_⟩
      intro w hw
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      refine ⟨.leaf (.inl {i}),Or.inl ⟨_,rfl⟩,?_⟩
      exact ⟨by simp [Regular],by simp [Wire.jobs,atom],fun z _ => by simp [Binary.Tree.eval,interpret,lit,atom]⟩
    | append_singleton ops g ih =>
      simpa only [run,List.foldl_append,List.foldl_cons,List.foldl_nil] using stepModel (run_valid 14 ops).1 g ih
  obtain ⟨book,built,count,tracked⟩ := all gs
  obtain ⟨e,ready,faith⟩ := portHas tracked out
  exact ⟨book,e,built,ready,faith,count⟩

theorem circuit (H : Graph) (J : Finset (Product 14)) (gs : List Op) (out : ℕ) :
    let s := run 14 gs
    let w := s.wires.getD out default
    ∃ e : Expr, Faithful H J w e ∧ e.vars.card ≤ spent H J s+1 ∧
      (e.vars.card=spent H J s+1 → e.inputs.Nodup) := by
  obtain ⟨book,e,built,ready,faith,count⟩ := circuitBook H J gs out
  have cap := Binary.inputBudget built ready
  rw [count] at cap
  exact ⟨e,faith,cap⟩

#print axioms circuit
end Checkpoint125.Contract
