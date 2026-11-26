import OrbitSearch
import PEqualNP.Outside.L_meta_9338

namespace Checkpoint135
open PEqualNP.Outside.L_meta_9338 (V Box bit hit legal)
open Function

structure Rotation where
  row : V → V
  col : V → V

namespace Rotation
def stable (R : Rotation) (b : Box) : Prop :=
  ∀ i j, hit b i j → hit b (R.row i) (R.col j)

def meets (R : Rotation) (p : ℕ) (b : Box) (i j : V) : Prop :=
  ∃ t : Fin p, hit b ((R.row^[t.val]) i) ((R.col^[t.val]) j)

theorem iterHit {R : Rotation} {b : Box} (closed : R.stable b) {i j : V}
    (h : hit b i j) (k : ℕ) : hit b ((R.row^[k]) i) ((R.col^[k]) j) := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [Function.iterate_succ_apply'] using closed _ _ ih

/-- Representatives on the boundary have independently rotated row/column coordinates
which meet a forbidden entry. Each such representative must use a moving rectangle. -/
theorem boundary {n s p : ℕ} [NeZero p] (R : Rotation) (D : Search n s p)
    (pt : Fin n → V × V)
    (zero : ∀ i, bit (pt i).1 (pt i).2=false)
    (esc : ∀ i, ∃ a b : Fin p,bit ((R.row^[a.val]) (pt i).1) ((R.col^[b.val]) (pt i).2)=true)
    (cross : ∀ (i j : Fin n) (a b : Fin p),
      bit ((R.row^[a.val]) (pt i).1) ((R.col^[b.val]) (pt j).2)=false →
      bit ((R.row^[b.val]) (pt j).1) ((R.col^[a.val]) (pt i).2)=false →
      D.pattern i j (b-a)=true)
    (blocked : ∀ f,¬D.compatible f)
    (family : Fin s → Box) (law : ∀t, legal (family t))
    (cover : ∀ x y : V, bit x y=false →
      (∃ b, legal b ∧ R.stable b ∧ hit b x y) ∨ ∃t, R.meets p (family t) x y) : False := by
  have chooseLabel (i : Fin n) : ∃ u : Label s p, hit (family u.1)
      ((R.row^[u.2.val]) (pt i).1) ((R.col^[u.2.val]) (pt i).2) := by
    rcases cover _ _ (zero i) with ⟨b,good,closed,h⟩ | ⟨t,k,h⟩
    · obtain ⟨u,v,forbidden⟩ := esc i
      have contradiction := good _ (iterHit closed h u.val).1 _ (iterHit closed h v.val).2
      rw [forbidden] at contradiction
      contradiction
    · exact ⟨(t,k),h⟩
  choose f hf using chooseLabel
  apply blocked f
  intro i j
  by_cases eq : (f i).1=(f j).1
  · right
    have a := hf i
    have b := hf j
    rw [←eq] at b
    exact cross _ _ _ _ (law _ _ a.1 _ b.2) (law _ _ b.1 _ a.2)
  · exact Or.inl eq

end Rotation
end Checkpoint135
