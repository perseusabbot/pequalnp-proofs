import InducedModel

namespace Checkpoint132.Induced
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint130.Prune
open PEqualNP.Outside.L_meta_3004_aux.Controls

def kept {t : ℕ} (u : ℕ) (v : Slot t) := u.testBit v.val.val

def Good (t u hot : ℕ) : Prop :=
  (∀ v : Slot u,t.testBit v.val.val=true) ∧
  (∀ a b : Slot t,a.val.val=hot → kept u a=false → adj a b → kept u b=false)
instance (t u hot) : Decidable (Good t u hot) := by unfold Good; infer_instance

def port {t} (u hot : ℕ) (v : Slot t) : Value (Slot u) :=
  if h : kept u v=true then .wire ⟨v.val,h⟩ else .bit (v.val.val==hot)

def lift {t u} (hot : ℕ) (z : Slot u→Bool) (v : Slot t) : Bool :=
  if h : kept u v=true then z ⟨v.val,h⟩ else v.val.val==hot

private theorem portOn {t u} (hot : ℕ) (z : Slot u→Bool) (v : Slot t) :
    (port u hot v).truth (fun b => z b=true) ↔ lift hot z v=true := by
  by_cases h : kept u v=true <;> simp [port,lift,h,Value.truth]

theorem liftCorrect {t u hot} (good : Good t u hot) (z : Slot u→Bool) :
    accepts (lift (t:=t) hot z) ↔ accepts z := by
  obtain ⟨sub,safe⟩ := good
  have present {a b : Slot t} (ab : adj a b) (ha : lift hot z a=true) (hb : lift hot z b=true) :
      kept u a=true := by
    by_contra absent
    have zero : kept u a=false := Bool.eq_false_iff.mpr absent
    have ah : a.val.val=hot := by simpa [lift,absent] using ha
    have bz := safe a b ah zero ab
    have bh : b.val.val=hot := by simpa [lift,bz] using hb
    have eq : a.val=b.val := Fin.ext (ah.trans bh.symm)
    exact G.loopless.irrefl _ (eq ▸ (show G.Adj a.val b.val from ab))
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    have ka := present edge ha hb
    have kb := present (a:=b) (b:=a) edge.symm hb ha
    exact ⟨⟨a.val,ka⟩,⟨b.val,kb⟩,edge,by simpa [lift,ka] using ha,by simpa [lift,kb] using hb⟩
  · rintro ⟨a,b,edge,ha,hb⟩
    let x : Slot t := ⟨a.val,sub a⟩
    let y : Slot t := ⟨b.val,sub b⟩
    have kx : kept u x=true := a.property
    have ky : kept u y=true := b.property
    exact ⟨x,y,edge,by simpa [lift,kx,x] using ha,by simpa [lift,ky,y] using hb⟩

def merge {A : Type} (op : Bool) : Value A→Value A→Value A
  | .bit b,v => if b=op then .bit b else v
  | .wire a,.bit b => if b=op then .bit b else .wire a
  | .wire _,.wire _ => .bit false

private theorem mergeOn {A : Type} (op : Bool) (a b : Value A) (used : a.port=none ∨ b.port=none)
    (ρ : A→Prop) : (merge op a b).truth ρ ↔ if op then a.truth ρ ∨ b.truth ρ else a.truth ρ ∧ b.truth ρ := by
  cases a with
  | bit x => cases x <;> cases op <;> simp [merge,Value.truth]
  | wire x => cases b with
    | wire y => simp [Value.port] at used
    | bit y => cases y <;> cases op <;> simp [merge,Value.truth]

def transPort {t} (u hot : ℕ) (op : Bool) (x y : Slot t) : Option (Slot t)→Value (Slot u)
  | some a => port u hot a
  | none => merge op (port u hot x) (port u hot y)

def outside {t} (u : ℕ) (x y : Slot t) : Prop := kept u x=false ∨ kept u y=false
instance {t} (u) (x y : Slot t) : Decidable (outside u x y) := by unfold outside; infer_instance

private theorem translates {t u hot} (op : Bool) (x y : Slot t) (cut : outside u x y)
    (z : Slot u→Bool) (a : Option (Slot t)) :
    (transPort u hot op x y a).truth (fun w => z w=true) ↔ extend op x y (fun w => lift hot z w=true) a := by
  cases a with
  | some v => exact portOn hot z v
  | none =>
    have rem : (port u hot x).port=none ∨ (port u hot y).port=none :=
      cut.elim (fun h => Or.inl (by simp [port,h,Value.port])) (fun h => Or.inr (by simp [port,h,Value.port]))
    simpa only [transPort,extend,portOn] using mergeOn op (port u hot x) (port u hot y) rem (fun w => z w=true)

def fixedOld {t} (u : ℕ) (op : Bool) (x y : Slot t) : Finset (Slot t) :=
  univ.filter fun a => kept u a=false ∧ ∃ w : Slot t,witness op x y a w

def price {t} (u hot : ℕ) (op : Bool) (x y : Slot t) : ℕ :=
  (fixedOld u op x y).card + if (transPort u hot op x y none).port=none then 1 else 0

theorem restriction {t u hot} (good : Good t u hot) (op : Bool) (x y : Slot t) (ne : x≠y)
    (cut : outside u x y) (yes : Yes u) (no : No u)
    {gs : List (Binary.Tree (Option (Slot t)))} {e : Binary.Tree (Option (Slot t))}
    (hb : Built gs) (hr : Ready gs e) (fresh : none∈e.vars)
    (ok : Fits (fun z => extend op x y (pv z)) (fun z => extend op x y (nv z)) e) :
    ∃ book : List (Binary.Tree (Slot u)), ∃ leaf, Built book ∧ Ready book leaf ∧ Fits pv nv leaf ∧
      book.length + price u hot op x y ≤ gs.length := by
  let φ := transPort u hot op x y
  let px (r : Yes u) : Yes t := ⟨lift hot r.val,(liftCorrect good _).mpr r.property⟩
  let nx (r : No u) : No t := ⟨lift hot r.val,fun h => r.property ((liftCorrect good _).mp h)⟩
  have hi (r : Yes u) (a) : extend op x y (pv (px r)) a → (φ a).truth (pv r) :=
    (translates op x y cut r.val a).mpr
  have lo (r : No u) (a) : (φ a).truth (nv r) → extend op x y (nv (nx r)) a :=
    (translates op x y cut r.val a).mp
  let old := (fixedOld u op x y).image some
  let fixed := if (φ none).port=none then insert none old else old
  have neededOld (a) (ha : a∈old) : a∈e.vars ∧ (φ a).port=none := by
    obtain ⟨v,hv,rfl⟩ := mem_image.mp ha
    obtain ⟨absent,w,hw⟩ := (mem_filter.mp hv).2
    exact ⟨cutUsed op x y v w ne hw ok,by simp [φ,transPort,port,absent,Value.port]⟩
  have need (a) (ha : a∈fixed) : a∈e.vars ∧ (φ a).port=none := by
    by_cases h : (φ none).port=none
    · rcases mem_insert.mp (show a∈insert none old from by simpa [fixed,h] using ha) with rfl|oldMem
      · exact ⟨fresh,h⟩
      · exact neededOld a oldMem
    · exact neededOld a (by simpa [fixed,h] using ha)
  have size : fixed.card=price u hot op x y := by
    by_cases h : (φ none).port=none
    · simp [fixed,old,price,φ] at h ⊢
      simp [h,card_image_of_injective _ (Option.some_injective _)]
    · simp [fixed,old,price,φ] at h ⊢
      simp [h,card_image_of_injective _ (Option.some_injective _)]
  obtain ⟨book,leaf,built,ready,fit,cost⟩ := signedProjection hb hr ok φ pv nv px nx hi lo yes no fixed need
  exact ⟨book,leaf,built,ready,fit,size ▸ cost⟩

def hasEdge (t : ℕ) := ∃ a b : Slot t,adj a b
instance (t) : Decidable (hasEdge t) := by unfold hasEdge; infer_instance

theorem fromChoices {t k : ℕ}
    (choices : ∀ (op : Bool) (x y : Slot t), x≠y → ∃ u hot L, Good t u hot ∧ hasEdge u ∧ outside u x y ∧
      Floor u L ∧ k≤1+L+price u hot op x y) : Floor t k := by
  intro book e hb hr fit
  obtain ⟨op,x,y,ne,gs,s,built,ready,count,fresh,ok⟩ := firstDistinct noLeaf hb hr fit
  obtain ⟨u,hot,L,good,⟨a,b,edge⟩,cut,floor,amount⟩ := choices op x y ne
  let yes : Yes u := ⟨fun _ => true,⟨a,b,edge,rfl,rfl⟩⟩
  let no : No u := ⟨fun _ => false,by rintro ⟨_,_,_,h,_⟩; contradiction⟩
  obtain ⟨qs,out,bq,rq,rows,paid⟩ := restriction good op x y ne cut yes no built ready fresh ok
  have lower := floor qs out bq rq rows
  omega

#print axioms liftCorrect
#print axioms restriction
#print axioms fromChoices
end Checkpoint132.Induced
