import BinaryBudget

namespace Checkpoint126.Zero
open Finset Checkpoint125 Checkpoint125.Binary
variable {A B : Type} [DecidableEq A] [DecidableEq B]

def combine (op : Bool) : Option (Binary.Tree B) → Option (Binary.Tree B) → Option (Binary.Tree B)
  | some a,some b => some (.gate op a b)
  | a,b => if op then a.or b else none

def reduce (f : A → Option B) : Binary.Tree A → Option (Binary.Tree B)
  | .leaf x => (f x).map Binary.Tree.leaf
  | .gate op a b => combine op (reduce f a) (reduce f b)

def emit (f : A → Option B) : Binary.Tree A → Option (Binary.Tree B)
  | .leaf _ => none
  | .gate op a b => do return .gate op (←reduce f a) (←reduce f b)

def value (ρ : B→Prop) (e : Option (Binary.Tree B)) := e.elim False (fun t => t.eval ρ)

omit [DecidableEq A] [DecidableEq B] in
theorem semantics (f : A→Option B) (ρ : B→Prop) (e : Binary.Tree A) :
    value ρ (reduce f e) ↔ e.eval (fun x => (f x).elim False ρ) := by
  induction e with
  | leaf x => cases h : f x <;> simp [reduce,h,value,Binary.Tree.eval]
  | gate op a b ia ib =>
    cases op <;> cases ha : reduce f a <;> cases hb : reduce f b <;>
      simp [reduce,combine,value,ha,hb,Binary.Tree.eval] at ia ib ⊢ <;> tauto

omit [DecidableEq A] [DecidableEq B] in
theorem library (f : A→Option B) {gs : List (Binary.Tree A)} (built : Built gs) :
    Built (gs.filterMap (emit f)) ∧ ∀ e, Ready gs e → ∀ x, reduce f e=some x →
      Ready (gs.filterMap (emit f)) x := by
  induction gs with
  | nil =>
    refine ⟨trivial,?_⟩
    intro e h x ev
    obtain ⟨v,rfl⟩ := h.elim id (by simp)
    cases h : f v <;> simp_all [reduce,Ready]
    exact ⟨_,ev.symm⟩
  | cons g gs ih =>
    obtain ⟨prev,op,a,b,rfl,ra,rb⟩ := built
    obtain ⟨ok,old⟩ := ih prev
    have lift {e} (h : Ready (gs.filterMap (emit f)) e) :
        Ready ((Binary.Tree.gate op a b::gs).filterMap (emit f)) e := by
      rcases h with lit|member
      · exact Or.inl lit
      · exact Or.inr (List.mem_filterMap.mpr (by
          obtain ⟨u,hu,eu⟩ := List.mem_filterMap.mp member
          exact ⟨u,List.mem_cons_of_mem _ hu,eu⟩))
    have fresh (x) (h : reduce f (.gate op a b)=some x) :
        Ready ((Binary.Tree.gate op a b::gs).filterMap (emit f)) x := by
      cases ha : reduce f a with
      | none =>
        cases hb : reduce f b with
        | none => cases op <;> simp [reduce,combine,ha,hb] at h
        | some u =>
          cases op <;> simp [reduce,combine,ha,hb] at h
          exact h ▸ lift (old _ rb u hb)
      | some u =>
        cases hb : reduce f b with
        | none =>
          cases op <;> simp [reduce,combine,ha,hb] at h
          exact h ▸ lift (old _ ra u ha)
        | some v =>
          simp [reduce,combine,ha,hb] at h
          exact Or.inr (List.mem_filterMap.mpr ⟨_,List.mem_cons_self ..,by simp [emit,ha,hb,h]⟩)
    constructor
    · cases ha : reduce f a <;> cases hb : reduce f b <;> simp [emit,ha,hb] <;>
        first | exact ok | exact ⟨ok,op,_,_,rfl,old _ ra _ ha,old _ rb _ hb⟩
    · rintro e (⟨v,rfl⟩|mem) x h
      · exact lift (old _ (Or.inl ⟨v,rfl⟩) _ h)
      · rcases List.mem_cons.mp mem with rfl|hm
        · exact fresh x h
        · exact lift (old _ (Or.inr hm) _ h)

private def zeros (f : A→Option B) (r : Finset (Binary.Tree A)) :=
  (r.filter fun t => reduce f t=none).card

omit [DecidableEq B] in
private theorem insertBound (f : A→Option B) (t : Binary.Tree A) (r : Finset (Binary.Tree A)) :
    zeros f (insert t r) ≤ zeros f r + (if reduce f t=none then 1 else 0) := by
  by_cases h : reduce f t=none
  · simpa [zeros,filter_insert,h] using card_insert_le t (r.filter fun e => reduce f e=none)
  · simp [zeros,filter_insert,h]

omit [DecidableEq A] [DecidableEq B] in
private theorem balance (f : A→Option B) (op : Bool) (a b : Binary.Tree A) :
    (if reduce f a=none then 1 else 0)+(if reduce f b=none then 1 else 0) ≤
    (if emit f (.gate op a b)=none then 1 else 0)+(if reduce f (.gate op a b)=none then 1 else 0) := by
  cases op <;> cases ha : reduce f a <;> cases hb : reduce f b <;> simp [reduce,emit,combine,ha,hb]

private def dropped (f : A→Option B) (gs : List (Binary.Tree A)) :=
  (gs.filter (fun e => (emit f e).isNone)).length

omit [DecidableEq B] in
private theorem frontier (f : A→Option B) (gs : List (Binary.Tree A)) (built : Built gs)
    (r : Finset (Binary.Tree A)) (ready : ∀ e∈r, Ready gs e) :
    ((r.biUnion Binary.Tree.vars).filter fun v => f v=none).card ≤ dropped f gs+zeros f r := by
  classical
  induction gs generalizing r with
  | nil =>
    have lit (t) (ht : t∈r) : ∃ v,t=Binary.Tree.leaf v := (ready t ht).elim id (by simp)
    let Z := r.filter fun e => reduce f e=none
    have eq : (r.biUnion Binary.Tree.vars).filter (fun v => f v=none)=Z.biUnion Binary.Tree.vars := by
      ext v
      simp only [mem_filter,mem_biUnion,Z]
      constructor
      · rintro ⟨⟨t,ht,hv⟩,z⟩
        obtain ⟨x,rfl⟩ := lit _ ht
        obtain rfl := mem_singleton.mp (by simpa only [Binary.Tree.leafVars] using hv)
        exact ⟨_,⟨ht,by simp [reduce,z]⟩,hv⟩
      · rintro ⟨t,⟨ht,z⟩,hv⟩
        obtain ⟨x,rfl⟩ := lit _ ht
        have eq : v=x := by simpa using hv
        exact ⟨⟨_,ht,hv⟩,by simpa [eq,reduce] using z⟩
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

/-- Each different zero input in the dependency cone pays for a deleted
gate when the restricted output survives. This also holds for shared gates. -/
theorem cost (f : A→Option B) {gs : List (Binary.Tree A)} (built : Built gs) {e : Binary.Tree A}
    (ready : Ready gs e) {x} (live : reduce f e=some x) :
    (gs.filterMap (emit f)).length+(e.vars.filter fun v => f v=none).card ≤ gs.length := by
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

#print axioms cost
end Checkpoint126.Zero
