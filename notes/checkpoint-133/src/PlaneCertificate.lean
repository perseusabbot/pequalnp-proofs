import PlaneOrbit

namespace Checkpoint133.Plane

structure Entry where
  l : Window
  r : Window
  i : V
  j : V
  edges : ℕ
  deriving Inhabited

def Entry.child (e : Entry) (side : Bool) (q : H) :=
  (e.edges >>> (13*((if side then 7 else 0)+q.val))) % 8192

def Entry.next (e : Entry) (side : Bool) (q : H) :=
  let i := move q e.i
  let j := move q e.j
  if side then (e.l,push e.r i j) else (push e.l i j,e.r)

def Verified (T : ℕ→Entry) (n : ℕ) : Prop :=
  let e := T n
  zeroCell e.i e.j ∧ ∀ (side : Bool) (q : H), possible (if side then e.r else e.l) q e.i e.j →
    let k := e.child side q
    k<n ∧ ((T k).l,(T k).r)=e.next side q
instance (T n) : Decidable (Verified T n) := by unfold Verified; infer_instance

theorem fromTable (T : ℕ→Entry) (n : ℕ) (checks : ∀ j≤n,Verified T j) : Dead (T n).l (T n).r := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain ⟨z,edges⟩ := checks n (by rfl)
    have go (side : Bool) (q : H) (p : possible (if side then (T n).r else (T n).l) q (T n).i (T n).j) :
        Dead ((T n).next side q).1 ((T n).next side q).2 := by
      obtain ⟨less,matchState⟩ := edges side q p
      rw [← matchState]
      exact ih _ less (fun j hj => checks j (hj.trans less.le))
    apply branch z
    · intro q p
      exact go false q p
    · intro q p
      exact go true q p

def checkBlock (T : ℕ→Entry) (base len : ℕ) : Bool :=
  (List.range len).all fun j => decide (Verified T (base+j))
theorem inBlock {T : ℕ→Entry} {base len j : ℕ} (ok : checkBlock T base len=true) (lo : base≤j) (hi : j<base+len) : Verified T j := by
  have eq := List.all_eq_true.mp ok (j-base) (List.mem_range.mpr (by omega))
  exact (show base+(j-base)=j by omega) ▸ of_decide_eq_true eq

#print axioms fromTable
end Checkpoint133.Plane
