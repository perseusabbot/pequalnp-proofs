import FamilyBound
import MixedCertificate
import Four1Sound
import Four4Sound
import Four6Sound
import Four13Sound
import Move2Sound
import Move3Sound
import Fixed2Sound
import Fixed3Sound

namespace Checkpoint134
open PEqualNP.Outside.L_meta_9338 (V Box legal bit)
set_option maxHeartbeats 0
private theorem fourTests {b : Book 147} (s : Sound b) (ranks : TileIndex→ℕ) (k : Actions.Class)
    (pass : ∀i,Passed b (tally b.coin (masks i)) (ranks i) 4=true)
    (marked : ∀z : Cell,b.coin z≠0 → bit (emb (rowOf z)) (colOf z)=false ∧
      ¬FixedPool.contains 0 (emb (rowOf z)) (colOf z) ∧
      ¬FixedPool.contains (Actions.rep k) (emb (rowOf z)) (colOf z))
    (a : Fin 4→Box) (g : ∀t,legal (a t)) (cov : PairSlots k a) : False := by
  choose idx project using fun t => projectTile (a t) (g t)
  apply rankedImpossible s 4 (by decide) masks ranks pass idx
  intro z nz
  obtain ⟨zero,h0,h1⟩ := marked z nz
  rcases cov _ _ zero with (h|h)|⟨t,h⟩
  · exact (h0 h).elim
  · exact (h1 h).elim
  · exact ⟨t,project t z h⟩

theorem noFourFrom
    (hFour1 : ∀i : TileIndex,Passed Four1.book (tally Four1.book.coin (masks i)) (Four1.rank i.val) 4=true)
    (hFour4 : ∀i : TileIndex,Passed Four4.book (tally Four4.book.coin (masks i)) (Four4.rank i.val) 4=true)
    (hFour6 : ∀i : TileIndex,Passed Four6.book (tally Four6.book.coin (masks i)) (Four6.rank i.val) 4=true)
    (hFour13 : ∀i : TileIndex,Passed Four13.book (tally Four13.book.coin (masks i)) (Four13.rank i.val) 4=true)
    (k : Actions.Class) (a : Fin 4→Box) (g : ∀t,legal (a t)) (cov : PairSlots k a) : False := by
  fin_cases k
  · exact fourTests Four1.sound (fun i => Four1.rank i.val) _ hFour1 (by decide +kernel) a g cov
  · exact fourTests Four4.sound (fun i => Four4.rank i.val) _ hFour4 (by decide +kernel) a g cov
  · exact fourTests Four6.sound (fun i => Four6.rank i.val) _ hFour6 (by decide +kernel) a g cov
  · exact fourTests Four13.sound (fun i => Four13.rank i.val) _ hFour13 (by decide +kernel) a g cov

private theorem mixedTests {b c : Book 147} {m f : ℕ} (sb : Sound b) (sc : Sound c)
    (size : b.n=c.n) (coins : b.coin=c.coin) (pos : 0<m)
    (ra : TileIndex→ℕ) (rd : FixedPool.Index→ℕ)
    (ma : ∀i,Accept b c m f (tally b.coin (masks i)) (ra i)=true)
    (fd : ∀i,Accept c b f m (tally c.coin (FixedPool.mask i)) (rd i)=true)
    (marked : ∀z : Cell,b.coin z≠0 → bit (emb (rowOf z)) (colOf z)=false)
    (a : Fin m→Box) (d : Fin f→FixedPool.Index) (g : ∀t,legal (a t)) (cov : Slots m f a d) : False := by
  choose idx project using fun t => projectTile (a t) (g t)
  apply mixedImpossible sb sc size coins pos (fun t => masks (idx t)) (fun t => ra (idx t))
    (fun t => FixedPool.mask (d t)) (fun t => rd (d t)) (fun t => ma (idx t)) (fun t => fd (d t))
  intro z nz
  rcases cov _ _ (marked z nz) with ⟨t,h⟩|⟨t,h⟩
  · exact Or.inr ⟨t,(FixedPool.maskAt ..).mp h⟩
  · exact Or.inl ⟨t,project t z h⟩
theorem noTwoFrom
    (hMove2 : ∀i : TileIndex,Accept Move2.book Fixed2.book 2 14 (tally Move2.book.coin (masks i)) (Move2.rank i.val)=true)
    (hFixed2 : ∀i : FixedPool.Index,Accept Fixed2.book Move2.book 14 2 (tally Fixed2.book.coin (FixedPool.mask i)) (Fixed2.rank i.val)=true)
    (a : Fin 2→Box) (d : Fin 14→FixedPool.Index)
    (g : ∀t,legal (a t)) (cov : Slots 2 14 a d) : False :=
  mixedTests Move2.sound Fixed2.sound rfl rfl (by decide)
    (fun i => Move2.rank i.val) (fun i => Fixed2.rank i.val)
    hMove2 hFixed2 (by decide +kernel) a d g cov
theorem noThreeFrom
    (hMove3 : ∀i : TileIndex,Accept Move3.book Fixed3.book 3 5 (tally Move3.book.coin (masks i)) (Move3.rank i.val)=true)
    (hFixed3 : ∀i : FixedPool.Index,Accept Fixed3.book Move3.book 5 3 (tally Fixed3.book.coin (FixedPool.mask i)) (Fixed3.rank i.val)=true)
    (a : Fin 3→Box) (d : Fin 5→FixedPool.Index)
    (g : ∀t,legal (a t)) (cov : Slots 3 5 a d) : False :=
  mixedTests Move3.sound Fixed3.sound rfl rfl (by decide)
    (fun i => Move3.rank i.val) (fun i => Fixed3.rank i.val)
    hMove3 hFixed3 (by decide +kernel) a d g cov

end Checkpoint134
