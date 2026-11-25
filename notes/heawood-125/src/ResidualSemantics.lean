import ResidualForms

namespace Checkpoint124.Shapes
variable {X σ : Type}

def term (ρ : ℕ → Set X) (t : Term) : Set X := {z | ∀ i∈t, z∈ρ i}
def eval (ρ : ℕ → Set X) (f : Form) : Set X := {z | ∃ t∈f, z∈term ρ t}

@[simp] theorem evalEmpty (ρ : ℕ → Set X) : eval ρ []=∅ := by ext z; simp [eval]
@[simp] theorem evalAtom (ρ : ℕ → Set X) (i) : eval ρ (atom i)=ρ i := by
  ext z; simp [eval,term,atom]
private theorem weakenTerm {ρ : ℕ → Set X} {t s : Term} (h : t⊆s) : term ρ s⊆term ρ t :=
  fun _ hz i hi => hz i (h hi)

private theorem evalAdd (ρ : ℕ → Set X) (t : Term) (f : Form) :
    eval ρ (addTerm t f)=term ρ t ∪ eval ρ f := by
  unfold addTerm
  split
  next h =>
    obtain ⟨u,hu,sub⟩ := List.any_eq_true.mp h
    ext z
    constructor
    · exact Or.inr
    · rintro (hz|hz)
      · exact ⟨u,hu,weakenTerm (of_decide_eq_true sub) hz⟩
      · exact hz
  next =>
    ext z
    constructor
    · rintro ⟨u,mem,hz⟩
      rcases List.mem_cons.mp mem with rfl|rest
      · exact Or.inl hz
      · exact Or.inr ⟨u,(List.mem_filter.mp rest).1,hz⟩
    · rintro (hz|⟨u,hu,hz⟩)
      · exact ⟨t,List.mem_cons_self ..,hz⟩
      · by_cases sub : t⊆u
        · exact ⟨t,List.mem_cons_self ..,weakenTerm sub hz⟩
        · exact ⟨u,List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hu,by simp [sub]⟩),hz⟩

private theorem evalReduce (ρ : ℕ → Set X) (f : Form) : eval ρ (reduce f)=eval ρ f := by
  induction f with
  | nil => rfl
  | cons t f ih =>
    change eval ρ (addTerm t (reduce f))=_
    rw [evalAdd,ih]
    ext z; simp [eval]

@[simp] theorem evalEither (ρ : ℕ → Set X) (a b) : eval ρ (either a b)=eval ρ a ∪ eval ρ b := by
  rw [either,evalReduce]
  ext z; simp [eval,or_and_right,exists_or]

@[simp] theorem evalBoth (ρ : ℕ → Set X) (a b) : eval ρ (both a b)=eval ρ a ∩ eval ρ b := by
  rw [both,evalReduce]
  ext z
  constructor
  · rintro ⟨t,mem,h⟩
    obtain ⟨u,hu,hm⟩ := List.mem_flatMap.mp mem
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    exact ⟨⟨u,hu,weakenTerm Finset.subset_union_left h⟩,⟨v,hv,weakenTerm Finset.subset_union_right h⟩⟩
  · rintro ⟨⟨u,hu,pu⟩,⟨v,hv,pv⟩⟩
    exact ⟨u∪v,List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv,rfl⟩⟩,
      fun i hi => (Finset.mem_union.mp hi).elim (pu i) (pv i)⟩

def Closed (X : Type) (pool : List Form) :=
  ∀ a∈pool, ∀ b∈pool, ∃ c∈pool, ∀ ρ : ℕ → Set X, eval ρ c=eval ρ a ∪ eval ρ b

private theorem closedAdd {P : List Form} (h : Closed X P) (f) : Closed X (P++P.map (either f)) := by
  intro a ha b hb
  rcases List.mem_append.mp ha with ha|ha <;> rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨c,hc,eq⟩ := h _ ha _ hb
    exact ⟨c,List.mem_append_left _ hc,eq⟩
  · obtain ⟨b,hb0,rfl⟩ := List.mem_map.mp hb
    obtain ⟨c,hc,eq⟩ := h _ ha _ hb0
    refine ⟨either f c,List.mem_append_right _ (List.mem_map.mpr ⟨c,hc,rfl⟩),fun ρ => ?_⟩
    rw [evalEither,evalEither,eq]; ext z; simp only [Set.mem_union]; tauto
  · obtain ⟨a,ha0,rfl⟩ := List.mem_map.mp ha
    obtain ⟨c,hc,eq⟩ := h _ ha0 _ hb
    refine ⟨either f c,List.mem_append_right _ (List.mem_map.mpr ⟨c,hc,rfl⟩),fun ρ => ?_⟩
    rw [evalEither,evalEither,eq]; ext z; simp only [Set.mem_union]; tauto
  · obtain ⟨a,ha0,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hb0,rfl⟩ := List.mem_map.mp hb
    obtain ⟨c,hc,eq⟩ := h _ ha0 _ hb0
    refine ⟨either f c,List.mem_append_right _ (List.mem_map.mpr ⟨c,hc,rfl⟩),fun ρ => ?_⟩
    simp only [evalEither,eq]; ext z; simp only [Set.mem_union]; tauto

theorem poolFacts {k q} (h : q∈frames k) : []∈q.pool ∧ Closed X q.pool := by
  induction k generalizing q with
  | zero =>
    obtain rfl := List.mem_singleton.mp h
    refine ⟨by simp [start],?_⟩
    rintro a ha b hb
    obtain rfl := List.mem_singleton.mp ha
    obtain rfl := List.mem_singleton.mp hb
    exact ⟨[],List.mem_singleton_self _,by simp⟩
  | succ k ih =>
    obtain ⟨p,hp,h⟩ := List.mem_flatMap.mp h
    obtain ⟨nil,old⟩ := ih hp
    have supplyOK (f n) : []∈(supply p f n).pool ∧ Closed X (supply p f n).pool :=
      ⟨List.mem_append_left _ nil,closedAdd old f⟩
    simp only [next,List.mem_append,List.mem_flatMap,List.mem_map] at h
    rcases h with (((⟨a,_,b,_,rfl⟩|⟨a,_,b,_,rfl⟩)|⟨a,_,rfl⟩)|⟨a,_,b,_,rfl⟩)
    · exact ⟨nil,old⟩
    all_goals exact supplyOK .. 

variable [Inhabited σ]
def Real (read : σ → Set X) (bank : List σ) (f : Form) (v : Set X) :=
  ∀ tail : List σ, eval (fun i => read ((bank++tail).getD i default)) f=v
def Has (read : σ → Set X) (bank : List σ) (pool : List Form) (v : Set X) :=
  ∃ f∈pool, Real read bank f v

theorem Real.extend {read : σ → Set X} {bank f v} (h : Real read bank f v) (more : List σ) :
    Real read (bank++more) f v := fun tail => by simpa only [List.append_assoc] using h (more++tail)
theorem Has.extend {read : σ → Set X} {bank pool v} (h : Has read bank pool v) (more : List σ) :
    Has read (bank++more) pool v := by
  obtain ⟨f,hf,ev⟩ := h
  exact ⟨f,hf,ev.extend more⟩
theorem Real.join {read : σ → Set X} {bank a b u v} (h : Real read bank a u) (k : Real read bank b v) :
    Real read bank (either a b) (u∪v) := fun tail => by rw [evalEither,h tail,k tail]
theorem Real.meet {read : σ → Set X} {bank a b u v} (h : Real read bank a u) (k : Real read bank b v) :
    Real read bank (both a b) (u∩v) := fun tail => by rw [evalBoth,h tail,k tail]
theorem Has.join {read : σ → Set X} {bank pool u v} (closed : Closed X pool)
    (h : Has read bank pool u) (k : Has read bank pool v) : Has read bank pool (u∪v) := by
  obtain ⟨a,ha,ea⟩ := h
  obtain ⟨b,hb,eb⟩ := k
  obtain ⟨c,hc,ep⟩ := closed _ ha _ hb
  exact ⟨c,hc,fun tail => by rw [ep,ea tail,eb tail]⟩

theorem leftAtom (read : σ → Set X) (bank : List σ) (a b : σ) :
    Real read (bank++[a,b]) (atom bank.length) (read a) := by
  intro tail
  rw [evalAtom]
  simp [List.append_assoc]
theorem rightAtom (read : σ → Set X) (bank : List σ) (a b : σ) :
    Real read (bank++[a,b]) (atom (bank.length+1)) (read b) := by
  intro tail
  rw [evalAtom]
  simp [List.append_assoc]

#print axioms evalBoth
#print axioms poolFacts
end Checkpoint124.Shapes
