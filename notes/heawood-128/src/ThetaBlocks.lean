import ThetaData

namespace Checkpoint128.Theta

def probe (k : ℕ) (s : List ℕ) (i : ℕ) : Bool :=
  ((pairs s)[i]?).any fun (x,y,r) =>
    follow (k+1) (search k) x y r (x &&& y) || follow (k+1) (search k) x y r (x ||| y)

def block (k r b : ℕ) := (List.range 3).any (fun j => probe k (roots.getD r []) (3*b+j))

theorem blocksClose (r : ℕ) (small : (pairs (roots.getD r [])).length≤66)
    (noLeaf : (roots.getD r []).any (fun x => distinction x==full)=false)
    (closed : ∀ b : Fin 22,block 10 r b=false) : search 11 (roots.getD r [])=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨p,hp,pass⟩ := List.any_eq_true.mp ((Bool.or_eq_true_iff.mp yes).resolve_left (fun h => Bool.noConfusion (noLeaf.symm.trans h)))
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  have marked : probe 10 (roots.getD r []) i=true := by
    simp only [probe,List.getElem?_eq_getElem hi,eq,Option.any_some]
    exact pass
  let b : Fin 22 := ⟨i/3,by omega⟩
  have bad : block 10 r b=true := List.any_eq_true.mpr ⟨i%3,List.mem_range.mpr (by omega),
    by simpa only [b,show 3*(i/3)+i%3=i by omega] using marked⟩
  rw [closed b] at bad
  contradiction
end Checkpoint128.Theta
