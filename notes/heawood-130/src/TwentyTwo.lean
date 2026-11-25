import CutTransfer
import FiveEmbeddings

namespace Checkpoint130.Heawood
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Prune
open PEqualNP.Outside.L_meta_3004_aux.Controls

abbrev Yes := {z : V→Bool // predicate z}
abbrev No := {z : V→Bool // ¬predicate z}
def positiveValue (z : Yes) (v : V) : Prop := z.val v=true
def negativeValue (z : No) (v : V) : Prop := z.val v=true

private theorem noLeaf (v : V) : ¬Fits positiveValue negativeValue (.leaf v) := by
  have single : ∀ u : V,¬predicate (fun w => decide (w=u)) := by decide +kernel
  intro h
  exact h.2 ⟨_,single v⟩ (by simp [Binary.Tree.eval,negativeValue])

/-- Choose a neighbor of the changing input that is distinct from and nonadjacent
to the input held fixed. These witnesses exist for every ordered pair. -/
private theorem neighbor : ∀ v w : V,v≠w → ∃ u : V,G.Adj v u ∧ u≠w ∧ ¬G.Adj u w := by
  decide +kernel

private theorem distinguish (v w : V) (ne : v≠w) (h : Bool) :
    ∃ a : Yes, ∃ b : No,(∀ u,u≠v → a.val u=b.val u) ∧ a.val w=h ∧ b.val w=h := by
  obtain ⟨u,adj,uw,away⟩ := neighbor v w ne
  let low (z : V) := decide (z=u) || (h && decide (z=w))
  let high (z : V) := decide (z=v) || low z
  have yes : predicate high := (orientation _).mpr ⟨v,u,adj,by simp [high],by simp [high,low]⟩
  have subset (z) (hz : low z=true) : z=u ∨ z=w := by
    simp [low] at hz
    tauto
  have no : ¬predicate low := by
    rintro good
    obtain ⟨s,t,st,hs,ht⟩ := (orientation _).mp good
    rcases subset s hs with rfl|rfl <;> rcases subset t ht with rfl|rfl
    · exact G.loopless.irrefl _ st
    · exact away st
    · exact away st.symm
    · exact G.loopless.irrefl _ st
  exact ⟨⟨high,yes⟩,⟨low,no⟩,fun z hz => by simp [high,hz],
    by simp [high,low,ne.symm,uw.symm],by simp [low,uw.symm]⟩

private theorem visible (op : Bool) {x y : V} (xy : x≠y) (t : Binary.Tree (Option V))
    (ok : Fits (fun z => extend op x y (positiveValue z)) (fun z => extend op x y (negativeValue z)) t)
    (v : V) : some v∈t.vars := by
  let w := if v=x then y else x
  have vw : v≠w := by by_cases eq : v=x <;> simp_all [w]
  obtain ⟨a,b,others,holdA,holdB⟩ := distinguish v w vw op
  apply mandatory ok _ a b
  rintro (_|u) ne
  · by_cases eq : v=x
    · have ha : a.val y=op := by simpa [w,eq] using holdA
      have hb : b.val y=op := by simpa [w,eq] using holdB
      cases op <;> simp [extend,positiveValue,negativeValue,ha,hb]
    · have ha : a.val x=op := by simpa [w,eq] using holdA
      have hb : b.val x=op := by simpa [w,eq] using holdB
      cases op <;> simp [extend,positiveValue,negativeValue,ha,hb]
  · change a.val u=true → b.val u=true
    rw [others u (fun eq => ne (congrArg some eq))]
    exact id

abbrev Port := {m : ℕ // m∈five.signals}
abbrev PosRow := {r : ℕ // r∈five.positives}
abbrev NegRow := {r : ℕ // r∈five.negatives}
def valPos (r : PosRow) (m : Port) : Prop := (m.val &&& r.val)!=0
def valNeg (r : NegRow) (m : Port) : Prop := (m.val &&& r.val)!=0

private def replace (q : List ℕ) : Option V→Value Port
  | none => .bit false
  | some v => if h : code q v∈five.signals then .wire ⟨_,h⟩ else .bit false

private theorem replaceSome (q : List ℕ) (good : Good q) (r : ℕ) (v : V) :
    (replace q (some v)).truth (fun m => (m.val &&& r)!=0) ↔ liftRow q r v=true := by
  by_cases h : code q v∈five.signals
  · simp [replace,h,Value.truth,liftRow]
  · have zero := (List.mem_cons.mp (good.2.1 v)).resolve_right h
    have off : 0∉five.signals := by decide +kernel
    simp [replace,Value.truth,liftRow,zero,off]

/-- Every correct full-graph binary circuit supplies a circuit six gates smaller
for the published ten-vertex test, including its free pair disjunction. -/
theorem sixGateReduction {book : List (Binary.Tree V)} (built : Built book) {e : Binary.Tree V}
    (ready : Ready book e) (truth : ∀ z : V→Bool,e.eval (fun v => z v=true) ↔ predicate z) :
    ∃ gs : List (Binary.Tree Port), ∃ t, Built gs ∧ Ready gs t ∧ Fits valPos valNeg t ∧
      gs.length+6≤book.length := by
  have root : Fits positiveValue negativeValue e :=
    ⟨fun z => (truth z.val).mpr z.property,fun z h => z.property ((truth z.val).mp h)⟩
  obtain ⟨op,x,y,xy,gs,t,hb,hr,count,fresh,ok⟩ := firstDistinct noLeaf built ready root
  obtain ⟨q,member,hx,hy⟩ := coverPair x y xy
  have good := goodEmbedding member
  let px (r : PosRow) : Yes := ⟨liftRow q r.val,good.2.2.1 _ r.property⟩
  let nx (r : NegRow) : No := ⟨liftRow q r.val,good.2.2.2 _ r.property⟩
  have noneOff (r : ℕ) : ¬extend op x y (fun v => liftRow q r v=true) none := by
    cases op <;> simp [extend,liftRow,hx,hy]
  have hi (r : PosRow) (a) : extend op x y (positiveValue (px r)) a → (replace q a).truth (valPos r) := by
    cases a with
    | none => exact fun h => False.elim (noneOff r.val h)
    | some v => exact (replaceSome q good r.val v).mpr
  have lo (r : NegRow) (a) : (replace q a).truth (valNeg r) → extend op x y (negativeValue (nx r)) a := by
    cases a with
    | none => simp [replace,Value.truth]
    | some v => exact (replaceSome q good r.val v).mp
  let fixed := insert none ((outside q).image some)
  have needed (a) (ha : a∈fixed) : a∈t.vars ∧ (replace q a).port=none := by
    rcases mem_insert.mp ha with rfl|old
    · exact ⟨fresh,rfl⟩
    obtain ⟨v,hv,rfl⟩ := mem_image.mp old
    have zero : code q v=0 := (mem_filter.mp hv).2
    have off : 0∉five.signals := by decide +kernel
    exact ⟨visible _ xy _ ok v,by simp [replace,zero,off,Value.port]⟩
  have p0 : 129∈five.positives := by decide +kernel
  have n0 : 31∈five.negatives := by decide +kernel
  obtain ⟨qs,out,hbuilt,hready,row,price⟩ := signedProjection hb hr ok (replace q) valPos valNeg px nx
    hi lo ⟨129,p0⟩ ⟨31,n0⟩ fixed needed
  have fiveFixed : fixed.card=5 := by
    simp [fixed,card_image_of_injective _ (Option.some_injective V),good.1]
  exact ⟨qs,out,hbuilt,hready,row,by omega⟩

/-- The only computational hypothesis here is the published fifteen-gate
exhaustion for the specific test in block 14, entry 6 of Checkpoint 129. -/
theorem twentyTwo (localFloor : ∀ gs : List (Binary.Tree Port), ∀ t, Built gs → Ready gs t →
    Fits valPos valNeg t → 16≤gs.length) {book : List (Binary.Tree V)} (built : Built book)
    {e : Binary.Tree V} (ready : Ready book e)
    (truth : ∀ z : V→Bool,e.eval (fun v => z v=true) ↔ predicate z) : 22≤book.length := by
  obtain ⟨gs,t,hb,hr,ok,count⟩ := sixGateReduction built ready truth
  have lower := localFloor gs t hb hr ok
  omega

#print axioms sixGateReduction
#print axioms twentyTwo
end Checkpoint130.Heawood
