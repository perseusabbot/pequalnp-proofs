import ThetaSearch

namespace Checkpoint128.Theta
open Finset Checkpoint125 Checkpoint126.Cherry
variable {A : Type} [DecidableEq A]

def Correct (σ : A→ℕ) (e : Binary.Tree A) : Prop :=
  ∀ i : Fin width, e.eval (fun a => (σ a).testBit i.val=true) ∧
    ¬e.eval (fun a => (σ a).testBit (width+i.val)=true)

private theorem bitCover {A : Type} (σ : A→ℕ) (s : List A) (i : ℕ) :
    (coveredBy (s.map σ)).testBit i=true ↔ ∃ a∈s,(distinction (σ a)).testBit i=true := by
  induction s with
  | nil => simp [coveredBy]
  | cons a s ih => simp only [List.map_cons,coveredBy,List.foldr_cons,Nat.testBit_or,Bool.or_eq_true_iff] at ih ⊢
                   simp [ih]

theorem allCovered {s : List A} {e : Binary.Tree A} (σ : A→ℕ)
    (enough : e.vars⊆s.toFinset) (yes : Correct σ e) : coveredBy (s.map σ)=full := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases lt : i<width
  · have yes' := yes ⟨i,lt⟩
    have witness : ∃ a∈e.vars,(σ a).testBit i=true ∧ (σ a).testBit (width+i)=false := by
      by_contra! no
      exact yes'.2 (e.mono (fun a ha on => Bool.eq_true_of_not_eq_false (no a ha on)) yes'.1)
    obtain ⟨a,ha,on,off⟩ := witness
    have bit := (bitCover σ s i).mpr ⟨a,List.mem_toFinset.mp (enough ha),by simp [distinction,full,lt,on,off]⟩
    simpa [full,lt] using bit
  · have off : (coveredBy (s.map σ)).testBit i=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨a,_,bit⟩ := (bitCover σ s i).mp h
      simp [distinction,full,lt] at bit
    simpa [full,lt] using off

private theorem pickOne {A : Type} {a : A} {s : List A} (ha : a∈s) :
    ∃ r,(a,r)∈picks s ∧ (a::r).Perm s := by
  induction s with
  | nil => simp at ha
  | cons b s ih =>
    rcases List.mem_cons.mp ha with rfl|mem
    · exact ⟨s,List.mem_cons_self ..,List.Perm.refl _⟩
    · obtain ⟨r,hr,perm⟩ := ih mem
      exact ⟨b::r,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,r),hr,rfl⟩),
        (List.Perm.swap ..).trans (perm.cons b)⟩

private theorem pickTwo {A : Type} {s : List A} {a b : A} (ha : a∈s) (hb : b∈s) (hne : a≠b) :
    ∃ x y r, (x,y,r)∈pairs s ∧ (x::y::r).Perm s ∧ ((a=x ∧ b=y) ∨ (a=y ∧ b=x)) := by
  induction s with
  | nil => simp at ha
  | cons t s ih =>
    rcases List.mem_cons.mp ha with rfl|ina
    · obtain ⟨r,hr,perm⟩ := pickOne ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨a,b,r,List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hr,rfl⟩),perm.cons _,Or.inl ⟨rfl,rfl⟩⟩
    rcases List.mem_cons.mp hb with rfl|inb
    · obtain ⟨r,hr,perm⟩ := pickOne (s:=s) ina
      exact ⟨b,a,r,List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hr,rfl⟩),perm.cons _,Or.inr ⟨rfl,rfl⟩⟩
    obtain ⟨x,y,r,hr,perm,xy⟩ := ih ina inb
    exact ⟨x,y,t::r,List.mem_append_right _ (List.mem_map.mpr ⟨(x,y,r),hr,rfl⟩),
      ((List.Perm.swap ..).cons x).trans ((List.Perm.swap ..).trans (perm.cons t)),xy⟩

private theorem mapPick {A B : Type} (f : A→B) {s : List A} {a r} (h : (a,r)∈picks s) :
    (f a,r.map f)∈picks (s.map f) := by
  induction s generalizing a r with
  | nil => simp [picks] at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with eq|old
    · cases eq; exact List.mem_cons_self ..
    · obtain ⟨⟨_,_⟩,mem,eq⟩ := List.mem_map.mp old
      cases eq
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,ih mem,rfl⟩)

private theorem mapPair {A B : Type} (f : A→B) {s : List A} {a b r} (h : (a,b,r)∈pairs s) :
    (f a,f b,r.map f)∈pairs (s.map f) := by
  induction s generalizing a b r with
  | nil => simp [pairs] at h
  | cons x xs ih =>
    rcases List.mem_append.mp h with pick|prev
    · obtain ⟨⟨_,_⟩,mem,eq⟩ := List.mem_map.mp pick
      cases eq
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_,mapPick f mem,rfl⟩)
    · obtain ⟨⟨_,_,_⟩,mem,eq⟩ := List.mem_map.mp prev
      cases eq
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih mem,rfl⟩)

private theorem bottomVars {op : Bool} {a b : A} (e : Binary.Tree A)
    (h : Binary.Tree.gate op (.leaf a) (.leaf b)∈nodes e) : a∈e.vars ∧ b∈e.vars := by
  induction e with
  | leaf => simp [nodes] at h
  | gate q x y ix iy =>
    rcases List.mem_cons.mp h with eq|old
    · cases eq; simp
    · rw [Binary.Tree.gateVars]
      rcases List.mem_append.mp old with l|r
      · obtain ⟨u,v⟩ := ix l; exact ⟨mem_union_left _ u,mem_union_left _ v⟩
      · obtain ⟨u,v⟩ := iy r; exact ⟨mem_union_right _ u,mem_union_right _ v⟩

private theorem untouched (op : Bool) (a b t : A) (e : Binary.Tree A) (ha : t≠a) (hb : t≠b) :
    some t∈(cut (.gate op (.leaf a) (.leaf b)) some none e).vars ↔ t∈e.vars := by
  induction e with
  | leaf x => simp [cut]
  | gate q x y ix iy =>
    by_cases same : Binary.Tree.gate q x y=.gate op (.leaf a) (.leaf b)
    · cases same; simp [cut,ha,hb]
    · simp [cut,same,ix,iy]

private theorem repeatVars (op : Bool) (a : A) (e : Binary.Tree A) :
    (cut (.gate op (.leaf a) (.leaf a)) id a e).vars=e.vars := by
  induction e with
  | leaf x => rfl
  | gate q x y ix iy =>
    by_cases same : Binary.Tree.gate q x y=.gate op (.leaf a) (.leaf a)
    · cases same; simp [cut]
    · simp [cut,same,ix,iy]

private theorem childFollows (k : ℕ) (go : List ℕ→Bool) (x y z : ℕ) (r : List ℕ)
    (keepX keepY : Bool) :
    let next := z::((if keepX then [x] else [])++(if keepY then [y] else [])++r)
    next.length≤k → coveredBy next=full → go next=true → follow k go x y r z=true := by
  cases keepX <;> cases keepY <;>
    simp [follow,coveredBy,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,
      Nat.or_comm,Nat.or_left_comm] <;> tauto

set_option maxHeartbeats 1500000 in
private theorem soundAux (n : ℕ) : ∀ (A : Type) [DecidableEq A] (σ : A→ℕ)
    (book : List (Binary.Tree A)) (e : Binary.Tree A) (s : List A) (k : ℕ),
    book.length=n → book.length≤k → Binary.Built book → Binary.Ready book e →
    s.Nodup → s.toFinset=e.vars → Correct σ e → search k (s.map σ)=true := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro A inst σ book e s k size bound built ready nd support yes
    rcases bottom e with ⟨a,rfl⟩|⟨op,a,b,occurs⟩
    · have la := allCovered (e:=Binary.Tree.leaf a) (s:=[a]) σ (by simp) yes
      have win : distinction (σ a)=full := by simpa [coveredBy] using la
      have member : a∈s := List.mem_toFinset.mp (support ▸ (by simp))
      have goal : (s.map σ).any (fun x => distinction x==full)=true :=
        List.any_eq_true.mpr ⟨σ a,List.mem_map.mpr ⟨a,member,rfl⟩,beq_iff_eq.mpr win⟩
      cases k <;> simp [search,goal]
    · let g : Binary.Tree A := .gate op (.leaf a) (.leaf b)
      have used : g∈book := listed built e ready g occurs
      by_cases same : a=b
      · subst b
        obtain ⟨ok,go⟩ := covered g id a built
        have len := oneLess id a used
        have ev : Correct σ (cut g id a e) := by
          have eq (i : ℕ) : (cut g id a e).eval (fun u => (σ u).testBit i=true) ↔
              e.eval (fun u => (σ u).testBit i=true) :=
            cutTruth g id a _ (by cases op <;> simp [g,Binary.Tree.eval]) e
          intro i
          exact ⟨(eq _).mpr (yes i).1,fun h => (yes i).2 ((eq _).mp h)⟩
        exact ih _ (by omega) _ σ _ _ s k rfl (by omega) ok (go _ ready) nd
          (support.trans (repeatVars op a e).symm) ev
      · have ⟨ha,hb⟩ := bottomVars e occurs
        obtain ⟨x,y,r,pair,perm,xy⟩ := pickTwo (s:=s)
          (List.mem_toFinset.mp (support ▸ ha)) (List.mem_toFinset.mp (support ▸ hb)) same
        have sr : (x::y::r).Nodup := perm.nodup_iff.mpr nd
        have different : x≠y := fun eq => (List.nodup_cons.mp sr).1 (by simp [eq])
        let z := mix op (σ x) (σ y)
        let σ' : Option A→ℕ := fun u => u.elim z σ
        let t := cut g some none e
        obtain ⟨ok,go⟩ := covered g some none built
        have len := oneLess some none used
        have ev : Correct σ' t := by
          have eq (i : ℕ) : t.eval (fun u => (σ' u).testBit i=true) ↔ e.eval (fun u => (σ u).testBit i=true) := by
            apply cutTruth g some none _
            rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases op <;>
              simp [g,σ',z,mix,Binary.Tree.eval,and_comm,or_comm]
          intro i
          exact ⟨(eq _).mpr (yes i).1,fun h => (yes i).2 ((eq _).mp h)⟩
        let carry := [x,y].filter (fun u => decide (some u∈t.vars))
        let ns : List (Option A) := none::((carry++r).map some)
        have sn : ns.Nodup := by
          have keep : (carry++r).Sublist (x::y::r) := (List.filter_sublist ..).append_right r
          exact List.nodup_cons.mpr ⟨by simp,(keep.nodup sr).map (Option.some_injective A)⟩
        have allvars : ns.toFinset=t.vars := by
          ext u
          cases u with
          | none => simp [ns,show none∈t.vars from fresh some none e occurs]
          | some u =>
            have fromR (hu : u∈r) : u≠x ∧ u≠y := by
              have d := List.nodup_cons.mp sr
              exact ⟨fun eq => d.1 (List.mem_cons_of_mem _ (eq ▸ hu)),fun eq => (List.nodup_cons.mp d.2).1 (eq ▸ hu)⟩
            by_cases ux : u=x
            · subst u
              simp [ns,carry,show x∉r from fun h => (fromR h).1 rfl]
            by_cases uy : u=y
            · subst u
              simp [ns,carry,show y∉r from fun h => (fromR h).2 rfl]
            have rem : some u∈t.vars ↔ u∈e.vars := by
              rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
              · exact untouched op _ _ u e ux uy
              · exact untouched op _ _ u e uy ux
            have inS : u∈e.vars ↔ u∈x::y::r := by rw [←support,List.mem_toFinset,perm.mem_iff]
            simp [ns,carry,ux,uy,rem,inS]
        cases k with
        | zero => omega
        | succ k =>
          have cap := (Binary.inputBudget ok (go e ready)).1
          rw [←allvars,List.toFinset_card_of_nodup sn] at cap
          have budget' : ns.length≤k+1 := by omega
          have child := ih _ (by omega) _ σ' _ t ns k rfl (by omega) ok (go e ready) sn allvars ev
          have cov := allCovered (s:=ns) σ' allvars.ge ev
          let kx := decide (some x∈t.vars)
          let ky := decide (some y∈t.vars)
          have form : ns.map σ'=z::((if kx then [σ x] else [])++(if ky then [σ y] else [])++r.map σ) := by
            by_cases hx : some x∈t.vars <;> by_cases hy : some y∈t.vars <;> simp [ns,carry,kx,ky,σ',hx,hy]
          have sl : (ns.map σ').length≤k+1 := by simpa using budget'
          rw [form] at sl cov child
          have okChild := childFollows (k+1) (search k) (σ x) (σ y) z (r.map σ) kx ky sl cov child
          apply Bool.or_eq_true_iff.mpr (Or.inr _)
          apply List.any_eq_true.mpr
          refine ⟨_,mapPair σ pair,?_⟩
          cases op <;> simp [z,mix] at okChild <;> simp [okChild]

/-- The exhaustive last-use search accepts every circuit within its gate cap,
including shared intermediate gates and repeated operands. -/
theorem searchNecessary (σ : A→ℕ) {book : List (Binary.Tree A)} {e : Binary.Tree A} {s : List A} {k : ℕ}
    (bound : book.length≤k) (built : Binary.Built book) (ready : Binary.Ready book e)
    (nd : s.Nodup) (inputs : s.toFinset=e.vars) (yes : Correct σ e) : search k (s.map σ)=true :=
  soundAux book.length A σ book e s k rfl bound built ready nd inputs yes

#print axioms searchNecessary
end Checkpoint128.Theta
