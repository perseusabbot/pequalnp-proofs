import FrameCore

namespace Checkpoint136
open PEqualNP.Outside.L_meta_9338 (V bit)
open MulAction

structure Rectangle where
  rows : Set V
  cols : Set V

namespace Rectangle

def Legal (b : Rectangle) := ∀r∈b.rows,∀c∈b.cols,bit r c=false
def Contains (b a : Rectangle) := a.rows⊆b.rows ∧ a.cols⊆b.cols
def Maximal (b : Rectangle) := Legal b ∧ ∀c,Legal c → Contains c b → c=b
def columns (s : Set V) : Set V := {c | ∀r∈s,bit r c=false}
def rowsFor (s : Set V) : Set V := {r | ∀c∈s,bit r c=false}
def extension (b : Rectangle) : Rectangle := ⟨rowsFor (columns b.rows),columns b.rows⟩
def move (f : Axis) (b : Rectangle) : Rectangle := ⟨row f '' b.rows,col f '' b.cols⟩

theorem extensionContains {b : Rectangle} (legal : Legal b) : Contains (extension b) b :=
  ⟨fun r hr _ hc => hc r hr,fun c hc r hr => legal r hr c hc⟩

theorem extensionMaximal (b : Rectangle) : Maximal (extension b) := by
  refine ⟨fun r hr c hc => hr c hc,?_⟩
  intro z law contains
  have rows : b.rows⊆(extension b).rows := fun r hr c hc => hc r hr
  have cs : z.cols=(extension b).cols := Set.Subset.antisymm
    (fun c hc r hr => law r (contains.1 (rows hr)) c hc) contains.2
  have rs : z.rows=(extension b).rows := Set.Subset.antisymm
    (fun r hr c hc => law r hr c (cs.symm ▸ hc)) contains.1
  cases z; exact Rectangle.mk.injEq _ _ _ _ |>.mpr ⟨rs,cs⟩

private theorem columns_move (f : Axis) (s : Set V) :
    columns (row f '' s)=col f '' columns s := by
  ext c
  obtain ⟨j,rfl⟩ := (col f).surjective c
  constructor
  · intro h
    exact ⟨j,fun r hr => (f.property r j).symm.trans (h _ ⟨r,hr,rfl⟩),rfl⟩
  · rintro ⟨k,hk,eq⟩ r ⟨p,hp,rfl⟩
    have : k=j := (col f).injective eq
    subst k
    exact (f.property p j).trans (hk p hp)

private theorem rows_move (f : Axis) (s : Set V) :
    rowsFor (col f '' s)=row f '' rowsFor s := by
  ext r
  obtain ⟨i,rfl⟩ := (row f).surjective r
  constructor
  · intro h
    exact ⟨i,fun c hc => (f.property i c).symm.trans (h _ ⟨c,hc,rfl⟩),rfl⟩
  · rintro ⟨j,hj,eq⟩ c ⟨k,hk,rfl⟩
    have : j=i := (row f).injective eq
    subst j
    exact (f.property i k).trans (hj k hk)

theorem extension_move (f : Axis) (b : Rectangle) :
    extension (move f b)=move f (extension b) := by
  simp [extension,move,columns_move,rows_move]

/-- Enlarging one rectangle cannot increase the orbit cost when all its stabilizers
also fix the enlargement. -/
theorem orbitCost {G : Type*} [Group G] [MulAction G Rectangle] [Finite G]
    {b c : Rectangle} (stable : ∀g : G,g • b=b → g • c=c) :
    Nat.card (orbit G c) ≤ Nat.card (orbit G b) := by
  classical
  let choose (x : orbit G b) : G := Classical.choose x.property
  have spec (x : orbit G b) : choose x • b=x.val := Classical.choose_spec x.property
  let send (x : orbit G b) : orbit G c := ⟨choose x • c,choose x,rfl⟩
  let : Finite (orbit G b) := Finite.of_surjective (fun g : G => (⟨g • b,g,rfl⟩ : orbit G b)) (by
    rintro ⟨_,g,rfl⟩; exact ⟨g,rfl⟩)
  apply Nat.card_le_card_of_surjective send
  rintro ⟨y,g,rfl⟩
  let x : orbit G b := ⟨g • b,g,rfl⟩
  refine ⟨x,Subtype.ext ?_⟩
  change choose x • c=g • c
  have hx : (g⁻¹*choose x) • b=b := by rw [mul_smul,spec]; change g⁻¹ • (g • b)=b; simp
  have hc := congrArg (fun z : Rectangle => g • z) (stable _ hx)
  simpa [mul_smul] using hc

/-- A moving orbit only needs maximal rectangles. A rectangle fixed by an
axis-exchanging group element is retained as a separate candidate. -/
theorem orbitCandidate {G : Type*} [Group G] [MulAction G Rectangle] [Finite G]
    (preservesAxes : G → Prop) (axis : ∀g : G,preservesAxes g → ∃f : Axis,∀b,g • b=move f b)
    (monotone : ∀g : G,∀b c,Contains c b → Contains (g • c) (g • b))
    (b : Rectangle) (legal : Legal b) :
    ∃c,Legal c ∧ (Maximal c ∨ ∃g : G,¬preservesAxes g ∧ g • c=c) ∧
      Nat.card (orbit G c)≤Nat.card (orbit G b) ∧
      ∀z∈orbit G b,∃w∈orbit G c,Contains w z := by
  classical
  by_cases h : ∃g : G,¬preservesAxes g ∧ g • b=b
  · exact ⟨b,legal,Or.inr h,le_rfl,fun z hz => ⟨z,hz,Set.Subset.rfl,Set.Subset.rfl⟩⟩
  · have stable (g : G) (hb : g • b=b) : g • extension b=extension b := by
      obtain ⟨f,hf⟩ := axis g (by by_contra nh; exact h ⟨g,nh,hb⟩)
      rw [hf,← extension_move,← hf,hb]
    refine ⟨extension b,(extensionMaximal b).1,Or.inl (extensionMaximal b),orbitCost stable,?_⟩
    rintro z ⟨g,rfl⟩
    exact ⟨g • extension b,⟨g,rfl⟩,monotone g _ _ (extensionContains legal)⟩

#print axioms extensionMaximal
#print axioms extension_move
#print axioms orbitCost
#print axioms orbitCandidate
end Rectangle
end Checkpoint136
