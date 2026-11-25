import SharedOR

namespace Checkpoint122.Pruning
open Finset StarUnion

abbrev Support (n : ℕ) := Finset (Fin n)
abbrev Product (n : ℕ) := Support n × Support n

def lit {n} (S : Support n) (z : Fin n → Bool) : Prop := ∃ v ∈ S, z v = true

structure Wire (n : ℕ) where
  pure : Bool
  raw : Support n
  tags : Finset (Option (Product n))
  full : (Fin n → Bool) → Bool

/-- A tag records an ordinary input product. The tag `none` records that a
suppressed nested AND can reach this wire through OR gates alone. -/
def Wire.jobs {n} (w : Wire n) := w.tags.eraseNone

instance {n} : Inhabited (Wire n) := ⟨⟨true,∅,∅,fun _ => false⟩⟩

def accepts {n} (w : Wire n) (z : Fin n → Bool) : Prop :=
  lit w.raw z ∨ ∃ p ∈ w.jobs, lit p.1 z ∧ lit p.2 z

def atom {n} (i : Fin n) : Wire n := ⟨true,{i},∅,fun z => z i⟩
def joinW {n} (a b : Wire n) : Wire n :=
  ⟨a.pure && b.pure,a.raw ∪ b.raw,a.tags ∪ b.tags,fun z => a.full z || b.full z⟩
def meetW {n} (a b : Wire n) : Wire n :=
  ⟨false,∅,{some (a.raw,b.raw)},fun z => a.full z && b.full z⟩
def cutW {n} (a b : Wire n) : Wire n := ⟨false,∅,{none},fun z => a.full z && b.full z⟩

structure Op where
  isOr : Bool
  left : ℕ
  right : ℕ
  deriving DecidableEq, Repr

structure State (n : ℕ) where
  wires : List (Wire n)
  bottom : List (Support n)
  top : List (Finset (Option (Product n)))
  products : List (Product n)
  dropped : ℕ
  bypass : ℕ

def initial (n : ℕ) : State n := ⟨List.ofFn atom,[],[],[],0,0⟩

def act {n} (s : State n) (a b : Wire n) (op : Bool) : State n :=
  match op, a.pure && b.pure with
  | true, true => ⟨s.wires++[joinW a b],(a.raw ∪ b.raw)::s.bottom,s.top,s.products,s.dropped,s.bypass⟩
  | true, false =>
    if a.pure || b.pure then ⟨s.wires++[joinW a b],s.bottom,s.top,s.products,s.dropped,s.bypass+1⟩
    else ⟨s.wires++[joinW a b],s.bottom,(a.tags ∪ b.tags)::s.top,s.products,s.dropped,s.bypass⟩
  | false, true => ⟨s.wires++[meetW a b],s.bottom,s.top,(a.raw,b.raw)::s.products,s.dropped,s.bypass⟩
  | false, false => ⟨s.wires++[cutW a b],s.bottom,s.top,s.products,s.dropped+1,s.bypass⟩

def step {n} (s : State n) (g : Op) := act s (s.wires.getD g.left default) (s.wires.getD g.right default) g.isOr
def run (n : ℕ) (gs : List Op) := gs.foldl step (initial n)
def cost {n} (s : State n) := s.bottom.length+s.top.length+s.products.length+s.dropped+s.bypass

structure Fits {n} (B : List (Support n)) (T : List (Finset (Option (Product n)))) (P : List (Product n))
    (d bypass : ℕ) (w : Wire n) : Prop where
  low : w.pure=true → Ready B w.raw
  empty : w.pure=true → w.tags=∅
  high : Ready T w.tags
  owned : ∀ p ∈ w.jobs, p ∈ P
  sound : ∀ z, accepts w z → w.full z = true
  marked : none ∈ w.tags → 0 < d
  same : none ∉ w.tags → ∀ z, w.full z = true → accepts w z
  origin : w.pure=false → bypass=0 → ∀ z, w.full z=true → ∃ p ∈ P, lit p.1 z ∧ lit p.2 z

structure Valid {n} (s : State n) : Prop where
  bottom : Built s.bottom
  top : Built s.top
  operands : ∀ p ∈ s.products, Ready s.bottom p.1 ∧ Ready s.bottom p.2
  wires : ∀ w ∈ s.wires, Fits s.bottom s.top s.products s.dropped s.bypass w

private theorem smallReady {V : Type*} [DecidableEq V] (l : List (Finset V)) : Ready l ∅ :=
  Or.inl (by simp)
private theorem readyAdd {V : Type*} [DecidableEq V] (x : Finset V) {l : List (Finset V)} {a : Finset V}
    (h : Ready l a) : Ready (x::l) a := h.imp_right (List.mem_cons_of_mem _)

private theorem fitsDefault {n B T P d x} : Fits B T P d x (default : Wire n) := by
  exact ⟨fun _ => smallReady _,fun _ => rfl,smallReady _,by simp [Wire.jobs,default,Inhabited.default],
    by simp [accepts,lit,Wire.jobs,default,Inhabited.default],by simp [default,Inhabited.default],by simp [default,Inhabited.default],by simp [default,Inhabited.default]⟩

private theorem initial_valid (n) : Valid (initial n) := by
  refine ⟨trivial,trivial,by simp [initial],?_⟩
  intro w hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  exact ⟨fun _ => Or.inl (by simp [atom]),fun _ => rfl,smallReady _,by simp [Wire.jobs,atom],
    by simp [accepts,lit,Wire.jobs,atom],by simp [atom],by simp [accepts,lit,Wire.jobs,atom],by simp [atom]⟩

theorem port {n} {s : State n} (h : Valid s) (i : ℕ) : Fits s.bottom s.top s.products s.dropped s.bypass (s.wires.getD i default) := by
  by_cases hi : i<s.wires.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h.wires _ (List.getElem_mem ..)
  · rw [List.getD_eq_default _ _ (by omega)]; exact fitsDefault

private theorem push {n} {s : State n} (hs : Valid s) {B T P d x} {w : Wire n}
    (b : Built B) (t : Built T) (p : ∀ q ∈ P, Ready B q.1 ∧ Ready B q.2)
    (bl : ∀ {u}, Ready s.bottom u → Ready B u) (tl : ∀ {u}, Ready s.top u → Ready T u)
    (pl : ∀ {u}, u ∈ s.products → u ∈ P) (dl : s.dropped ≤ d) (xl : s.bypass ≤ x) (fresh : Fits B T P d x w) :
    Valid (⟨s.wires++[w],B,T,P,d,x⟩ : State n) := by
  refine ⟨b,t,p,?_⟩
  intro old mem
  rcases List.mem_append.mp mem with ho | ho
  · have k := hs.wires _ ho
    refine ⟨fun e => bl (k.low e),k.empty,tl k.high,fun v hv => pl (k.owned v hv),k.sound,
      fun hm => (k.marked hm).trans_le dl,k.same,?_⟩
    intro imp zero z yes
    obtain ⟨q,hq,yes⟩ := k.origin imp (Nat.eq_zero_of_le_zero (xl.trans_eq zero)) z yes
    exact ⟨q,pl hq,yes⟩
  · obtain rfl := List.mem_singleton.mp ho
    exact fresh

private theorem join_accepts {n} (a b : Wire n) (z) :
    accepts (joinW a b) z ↔ accepts a z ∨ accepts b z := by
  unfold accepts lit
  simp only [joinW,Wire.jobs,eraseNone_union,mem_union,or_and_right,exists_or]
  constructor
  · rintro ((h|h)|(h|h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · rintro ((h|h)|(h|h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

private theorem pure_accepts {n B T P d x} {w : Wire n} (f : Fits B T P d x w) (hp : w.pure=true) (z) :
    accepts w z ↔ lit w.raw z := by simp [accepts,Wire.jobs,f.empty hp]

private theorem act_valid {n} {s : State n} (h : Valid s) {a b : Wire n}
    (fa : Fits s.bottom s.top s.products s.dropped s.bypass a) (fb : Fits s.bottom s.top s.products s.dropped s.bypass b) (op : Bool) :
    Valid (act s a b op) := by
  have soundOr (z) (v : accepts (joinW a b) z) : (joinW a b).full z=true := by
    rcases (join_accepts a b z).mp v with q | q
    · simp [joinW,fa.sound z q]
    · simp [joinW,fb.sound z q]
  have sameOr (no : none ∉ (joinW a b).tags) (z) (v : (joinW a b).full z=true) : accepts (joinW a b) z := by
    apply (join_accepts a b z).mpr
    have ab : none ∉ a.tags ∧ none ∉ b.tags := by simpa [joinW] using no
    exact (Bool.or_eq_true_iff.mp v).imp (fa.same ab.1 z) (fb.same ab.2 z)
  have markedOr (hm : none ∈ (joinW a b).tags) : 0 < s.dropped :=
    (mem_union.mp hm).elim fa.marked fb.marked
  have owned (p) (hp : p ∈ (joinW a b).jobs) :=
    ((show p ∈ a.jobs ∪ b.jobs by simpa only [joinW,Wire.jobs,eraseNone_union] using hp) |> mem_union.mp).elim (fa.owned p) (fb.owned p)
  cases eq : a.pure && b.pure with
  | true =>
    obtain ⟨ap,bp⟩ := Bool.and_eq_true_iff.mp eq
    cases op with
    | true =>
      simp only [act,eq]
      apply push (B := (a.raw ∪ b.raw)::s.bottom) h ⟨h.bottom,a.raw,b.raw,rfl,fa.low ap,fb.low bp⟩ h.top
        (fun p hp => ⟨readyAdd _ (h.operands p hp).1,readyAdd _ (h.operands p hp).2⟩)
        (readyAdd _) (fun h => h) (fun h => h) (by omega) (by omega)
      have empty : (joinW a b).tags=∅ := by simp [joinW,fa.empty ap,fb.empty bp]
      exact ⟨fun _ => Or.inr (List.mem_cons_self ..),fun _ => empty,empty ▸ smallReady _,owned,soundOr,markedOr,sameOr,by simp [joinW,eq]⟩
    | false =>
      simp only [act,eq]
      apply push h h.bottom h.top (fun p hp => (List.mem_cons.mp hp).elim (fun he => he ▸ ⟨fa.low ap,fb.low bp⟩) (h.operands p))
        (fun h => h) (fun h => h) (List.mem_cons_of_mem _) (by omega) (by omega)
      refine ⟨by simp [meetW],by simp [meetW],Or.inl (by simp [meetW]),?_,?_,by simp [meetW],?_,?_⟩
      · intro p hp; exact List.mem_cons.mpr (Or.inl (by simpa [Wire.jobs,meetW] using hp))
      · intro z v
        have both : lit a.raw z ∧ lit b.raw z := by simpa [accepts,Wire.jobs,meetW,lit] using v
        exact Bool.and_eq_true_iff.mpr ⟨fa.sound z ((pure_accepts fa ap z).mpr both.1),fb.sound z ((pure_accepts fb bp z).mpr both.2)⟩
      · intro _ z v
        obtain ⟨u,w⟩ := Bool.and_eq_true_iff.mp v
        have both := And.intro ((pure_accepts fa ap z).mp (fa.same (by simp [fa.empty ap]) z u)) ((pure_accepts fb bp z).mp (fb.same (by simp [fb.empty bp]) z w))
        simpa [accepts,Wire.jobs,meetW,lit] using both
      · intro _ _ z v
        obtain ⟨u,w⟩ := Bool.and_eq_true_iff.mp v
        exact ⟨_,List.mem_cons_self .., (pure_accepts fa ap z).mp (fa.same (by simp [fa.empty ap]) z u),
          (pure_accepts fb bp z).mp (fb.same (by simp [fb.empty bp]) z w)⟩
  | false =>
    cases op with
    | true =>
      cases mix : a.pure || b.pure with
      | true =>
        simp only [act,eq,mix,ite_true]
        apply push h h.bottom h.top h.operands (fun h => h) (fun h => h) (fun h => h) (by omega) (by omega)
        have ready : Ready s.top (joinW a b).tags := by
          rcases Bool.or_eq_true_iff.mp mix with ap|bp
          · simpa [joinW,fa.empty ap] using fb.high
          · simpa [joinW,fb.empty bp] using fa.high
        exact ⟨by simp [joinW,eq],by simp [joinW,eq],ready,owned,soundOr,markedOr,sameOr,by simp⟩
      | false =>
        simp only [act,eq,mix,Bool.false_eq_true,ite_false]
        apply push (T := (a.tags ∪ b.tags)::s.top) h h.bottom ⟨h.top,a.tags,b.tags,rfl,fa.high,fb.high⟩ h.operands
          (fun h => h) (readyAdd _) (fun h => h) (by omega) (by omega)
        refine ⟨by simp [joinW,eq],by simp [joinW,eq],Or.inr (List.mem_cons_self ..),owned,soundOr,markedOr,sameOr,?_⟩
        intro _ zero z yes
        obtain ⟨ap,bp⟩ := Bool.or_eq_false_iff.mp mix
        exact (Bool.or_eq_true_iff.mp yes).elim (fa.origin ap zero z) (fb.origin bp zero z)
    | false =>
      simp only [act,eq]
      apply push h h.bottom h.top h.operands (fun h => h) (fun h => h) (fun h => h) (by omega) (by omega)
      refine ⟨by simp [cutW],by simp [cutW],Or.inl (by simp [cutW]),by simp [cutW,Wire.jobs],by simp [cutW,accepts,lit,Wire.jobs],by simp,by simp [cutW],?_⟩
      intro _ zero z yes
      obtain ⟨u,v⟩ := Bool.and_eq_true_iff.mp yes
      cases ap : a.pure with
      | false => exact fa.origin ap zero z u
      | true => exact fb.origin (by simpa [ap] using eq) zero z v

private theorem act_cost {n} (s : State n) (a b : Wire n) (op : Bool) : cost (act s a b op) = cost s + 1 := by
  cases op <;> cases a1 : a.pure <;> cases b1 : b.pure <;> simp [act,cost,a1,b1] <;> omega

theorem run_valid (n) (gs : List Op) : Valid (run n gs) ∧ cost (run n gs) = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨initial_valid _,rfl⟩
  | append_singleton gs g ih =>
    obtain ⟨hv,hc⟩ := ih
    simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_append,List.length_singleton]
    exact ⟨act_valid hv (port hv _) (port hv _) _,(act_cost ..).trans (congrArg (·+1) hc)⟩

#print axioms run_valid
end Checkpoint122.Pruning
