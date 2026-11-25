import ZeroPruning

namespace Checkpoint130.Prune
open Finset Checkpoint125 Checkpoint125.Binary

inductive Value (A : Type) where
  | bit (b : Bool)
  | wire (a : A)
  deriving DecidableEq

def Value.port {A : Type} : Value A → Option A
  | .bit _ => none
  | .wire a => some a

def Value.truth {A : Type} (ρ : A→Prop) : Value A→Prop
  | .bit b => b=true
  | .wire a => ρ a

variable {A B : Type} [DecidableEq A] [DecidableEq B]

def combine (op : Bool) : Value (Binary.Tree B) → Value (Binary.Tree B) → Value (Binary.Tree B)
  | .wire a,.wire b => .wire (.gate op a b)
  | .bit a,b => if a=op then .bit a else b
  | a,.bit b => if b=op then .bit b else a

def specialize (f : A→Value B) : Binary.Tree A→Value (Binary.Tree B)
  | .leaf x => match f x with | .bit b => .bit b | .wire y => .wire (.leaf y)
  | .gate op a b => combine op (specialize f a) (specialize f b)

def reduce (f : A→Value B) (e : Binary.Tree A) := (specialize f e).port

def emit (f : A→Value B) : Binary.Tree A→Option (Binary.Tree B)
  | .leaf _ => none
  | .gate op a b => do return .gate op (←reduce f a) (←reduce f b)

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem reduceLeaf (f : A→Value B) (a : A) :
    reduce f (.leaf a)=(f a).port.map Binary.Tree.leaf := by
  cases h : f a <;> simp [reduce,specialize,h,Value.port]

omit [DecidableEq B] in
private theorem combineTruth (op : Bool) (a b : Value (Binary.Tree B)) (ρ : B→Prop) :
    (combine op a b).truth (fun e => e.eval ρ) ↔
      if op then a.truth (fun e => e.eval ρ) ∨ b.truth (fun e => e.eval ρ)
      else a.truth (fun e => e.eval ρ) ∧ b.truth (fun e => e.eval ρ) := by
  cases a with
  | bit x =>
    cases b with
    | bit y => cases x <;> cases y <;> cases op <;> simp [combine,Value.truth]
    | wire u => cases x <;> cases op <;> simp [combine,Value.truth]
  | wire u =>
    cases b with
    | bit y => cases y <;> cases op <;> simp [combine,Value.truth]
    | wire v => cases op <;> simp [combine,Value.truth,Binary.Tree.eval]

omit [DecidableEq A] [DecidableEq B] in
theorem semantics (f : A→Value B) (ρ : B→Prop) (e : Binary.Tree A) :
    (specialize f e).truth (fun t => t.eval ρ) ↔ e.eval (fun x => (f x).truth ρ) := by
  induction e with
  | leaf a => cases h : f a <;> simp [specialize,h,Value.truth,Binary.Tree.eval]
  | gate op a b ia ib => cases op <;> simp [specialize,combineTruth,Binary.Tree.eval,ia,ib]

omit [DecidableEq B] in
private theorem combineResult (op : Bool) (a b : Value (Binary.Tree B)) (x : Binary.Tree B)
    (h : (combine op a b).port=some x) :
    a.port=some x ∨ b.port=some x ∨
      ∃ u v,a.port=some u ∧ b.port=some v ∧ x=.gate op u v := by
  cases a with
  | bit c => cases c <;> cases op <;> simp_all [combine,Value.port]
  | wire u =>
    cases b with
    | bit c => cases c <;> cases op <;> simp_all [combine,Value.port]
    | wire v => simp_all [combine,Value.port]

omit [DecidableEq A] [DecidableEq B] in
theorem library (f : A→Value B) {gs : List (Binary.Tree A)} (built : Built gs) :
    Built (gs.filterMap (emit f)) ∧ ∀ e, Ready gs e → ∀ x, reduce f e=some x →
      Ready (gs.filterMap (emit f)) x := by
  induction gs with
  | nil =>
    refine ⟨trivial,?_⟩
    intro e he x eq
    obtain ⟨a,rfl⟩ := he.elim id (by simp)
    rw [reduceLeaf] at eq
    cases hf : f a <;> simp [hf,Value.port] at eq
    exact Or.inl ⟨_,eq.symm⟩
  | cons g gs ih =>
    obtain ⟨prev,op,a,b,rfl,ra,rb⟩ := built
    obtain ⟨ok,old⟩ := ih prev
    let g := Binary.Tree.gate op a b
    have lift {e} (h : Ready (gs.filterMap (emit f)) e) : Ready ((g::gs).filterMap (emit f)) e := by
      apply h.imp_right
      intro mem
      obtain ⟨u,hu,eu⟩ := List.mem_filterMap.mp mem
      exact List.mem_filterMap.mpr ⟨u,List.mem_cons_of_mem _ hu,eu⟩
    constructor
    · cases ha : reduce f a <;> cases hb : reduce f b <;> simp [emit,ha,hb] <;>
        first | exact ok | exact ⟨ok,op,_,_,rfl,old _ ra _ ha,old _ rb _ hb⟩
    · rintro e (lit|mem) x eq
      · exact lift (old _ (Or.inl lit) _ eq)
      · rcases List.mem_cons.mp mem with rfl|m
        · rcases combineResult op (specialize f a) (specialize f b) x eq with left|right|⟨u,v,hu,hv,rfl⟩
          · exact lift (old _ ra _ left)
          · exact lift (old _ rb _ right)
          · exact Or.inr (List.mem_filterMap.mpr ⟨_,List.mem_cons_self ..,by
              change (do return Binary.Tree.gate op (←(specialize f a).port) (←(specialize f b).port))=_
              simp [hu,hv]⟩)
        · exact lift (old _ (Or.inr m) _ eq)

private def zeros (f : A→Value B) (r : Finset (Binary.Tree A)) :=
  (r.filter fun t => reduce f t=none).card

omit [DecidableEq B] in
private theorem insertBound (f : A→Value B) (t : Binary.Tree A) (r : Finset (Binary.Tree A)) :
    zeros f (insert t r) ≤ zeros f r + (if reduce f t=none then 1 else 0) := by
  by_cases h : reduce f t=none
  · simpa [zeros,filter_insert,h] using card_insert_le t (r.filter fun e => reduce f e=none)
  · simp [zeros,filter_insert,h]

omit [DecidableEq A] [DecidableEq B] in
private theorem balance (f : A→Value B) (op : Bool) (a b : Binary.Tree A) :
    (if reduce f a=none then 1 else 0)+(if reduce f b=none then 1 else 0) ≤
    (if emit f (.gate op a b)=none then 1 else 0)+(if reduce f (.gate op a b)=none then 1 else 0) := by
  cases ha : specialize f a with
  | bit x =>
    cases hb : specialize f b with
    | bit y => cases x <;> cases y <;> cases op <;> simp [reduce,specialize,emit,combine,ha,hb,Value.port]
    | wire v => cases x <;> cases op <;> simp [reduce,specialize,emit,combine,ha,hb,Value.port]
  | wire u =>
    cases hb : specialize f b with
    | bit y => cases y <;> cases op <;> simp [reduce,specialize,emit,combine,ha,hb,Value.port]
    | wire v => cases op <;> simp [reduce,specialize,emit,combine,ha,hb,Value.port]

private def dropped (f : A→Value B) (gs : List (Binary.Tree A)) :=
  (gs.filter (fun e => (emit f e).isNone)).length

omit [DecidableEq B] in
private theorem frontier (f : A→Value B) (gs : List (Binary.Tree A)) (built : Built gs)
    (r : Finset (Binary.Tree A)) (ready : ∀ e∈r, Ready gs e) :
    ((r.biUnion Binary.Tree.vars).filter fun v => (f v).port=none).card ≤ dropped f gs+zeros f r := by
  classical
  induction gs generalizing r with
  | nil =>
    have lit (t) (ht : t∈r) : ∃ v,t=Binary.Tree.leaf v := (ready t ht).elim id (by simp)
    let Z := r.filter fun e => reduce f e=none
    have eq : (r.biUnion Binary.Tree.vars).filter (fun v => (f v).port=none)=Z.biUnion Binary.Tree.vars := by
      ext v
      simp only [mem_filter,mem_biUnion,Z]
      constructor
      · rintro ⟨⟨t,ht,hv⟩,z⟩
        obtain ⟨x,rfl⟩ := lit _ ht
        obtain rfl := mem_singleton.mp (by simpa only [Binary.Tree.leafVars] using hv)
        exact ⟨_,⟨ht,by simp [z]⟩,hv⟩
      · rintro ⟨t,⟨ht,z⟩,hv⟩
        obtain ⟨x,rfl⟩ := lit _ ht
        have eq : v=x := by simpa using hv
        exact ⟨⟨_,ht,hv⟩,by simpa [eq] using z⟩
    rw [eq]
    calc
      _ ≤ ∑ e∈Z,e.vars.card := card_biUnion_le
      _ = ∑ _∈Z,1 := sum_congr rfl (fun t ht => by obtain ⟨x,rfl⟩ := lit _ (mem_filter.mp ht).1; simp)
      _ = _ := by simp [dropped,zeros,Z]
  | cons g gs ih =>
    obtain ⟨prev,op,a,b,rfl,ra,rb⟩ := built
    let root := Binary.Tree.gate op a b
    have count : dropped f (root::gs)=dropped f gs+(if emit f root=none then 1 else 0) := by
      cases h : emit f root <;> simp [h,dropped,Nat.add_comm]
    by_cases used : root∈r
    · let rest := r.erase root
      let next := insert a (insert b rest)
      have rn (t) (ht : t∈next) : Ready gs t := by
        rcases mem_insert.mp ht with rfl|ht
        · exact ra
        rcases mem_insert.mp ht with rfl|ht
        · exact rb
        rcases ready t (mem_of_mem_erase ht) with lit|mem
        · exact Or.inl lit
        · exact Or.inr ((List.mem_cons.mp mem).resolve_left (ne_of_mem_erase ht))
      have restore : insert root rest=r := insert_erase used
      have uv : next.biUnion Binary.Tree.vars=r.biUnion Binary.Tree.vars := by
        rw [←restore]
        simp [next,root,union_assoc]
      have cap := ih prev next rn
      rw [uv] at cap
      have zrest : zeros f r=zeros f rest+(if reduce f root=none then 1 else 0) := by
        calc
          _ = zeros f (insert root rest) := congrArg (zeros f) restore.symm
          _ = _ := by
            have away : root∉rest.filter (fun t => reduce f t=none) := fun h => notMem_erase root r (mem_filter.mp h).1
            by_cases h : reduce f root=none <;> simp [zeros,filter_insert,h,away]
      have incA := insertBound f a (insert b rest)
      have incB := insertBound f b rest
      have step := balance f op a b
      change zeros f next ≤ _ at incA
      change _ ≤ (if emit f root=none then 1 else 0)+(if reduce f root=none then 1 else 0) at step
      change _ ≤ dropped f (root::gs)+zeros f r
      omega
    · have rn (t) (ht : t∈r) : Ready gs t := by
        rcases ready t ht with lit|mem
        · exact Or.inl lit
        · exact Or.inr ((List.mem_cons.mp mem).resolve_left (fun eq => used (by change Binary.Tree.gate op a b∈r; rwa [←eq])))
      have cap := ih prev r rn
      change _ ≤ dropped f (root::gs)+zeros f r
      omega

omit [DecidableEq B] in
/-- Each distinct input fixed to either Boolean constant in the dependency cone pays for a deleted
gate when the restricted output survives. This also holds for shared gates. -/
theorem cost (f : A→Value B) {gs : List (Binary.Tree A)} (built : Built gs) {e : Binary.Tree A}
    (ready : Ready gs e) {x} (live : reduce f e=some x) :
    (gs.filterMap (emit f)).length+(e.vars.filter fun v => (f v).port=none).card ≤ gs.length := by
  have h := frontier f gs built {e} (fun t ht => (mem_singleton.mp ht) ▸ ready)
  have zr : zeros f {e}=0 := by
    have he : reduce f e≠none := by rw [live]; simp
    simp [zeros,filter_singleton,he]
  rw [zr,Nat.add_zero,singleton_biUnion] at h
  have split : (gs.filterMap (emit f)).length+dropped f gs=gs.length := by
    clear h ready built
    induction gs with
    | nil => rfl
    | cons g gs ih => cases hg : emit f g <;> simp_all [dropped] <;> omega
  omega

#print axioms semantics
#print axioms library
#print axioms cost
end Checkpoint130.Prune
