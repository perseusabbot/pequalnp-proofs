import PostedModel
import OptimalStars

namespace Checkpoint122.Pruning
open Finset StarUnion SimpleGraph
open Checkpoint121.Heawood (points lines)
open PEqualNP.Outside.L_meta_3004_aux.Controls
open PEqualNP.Outside.L_meta_2268_aux.Normal

def star (v : V) := (nbr v).toFinset.image (fun u => s(v,u))
def incident (C : Finset V) := C.biUnion star

private theorem degree3 : ∀ v, (star v).card=3 := by decide +kernel

private theorem incidentCap (C : Finset V) : (incident C).card ≤ 3*C.card := calc
  (incident C).card ≤ ∑ v ∈ C, (star v).card := card_biUnion_le
  _ = 3*C.card := by simp [degree3,Nat.mul_comm]

-- Enumerate the specified triples and six-element subsets of each seven-vertex side.
attribute [local instance 2000] Finset.decidableDforallFinset

set_option maxHeartbeats 1500000

private def far (side fromSet : Finset V) := side.filter fun v => ∀ u ∈ fromSet, ¬ G.Adj u v

private theorem triples :
    (∀ A ∈ points.powersetCard 3, (far lines A).card≤1) ∧
    (∀ A ∈ lines.powersetCard 3, (far points A).card≤1) := by decide +kernel
private theorem singles : (∀ v ∈ lines, (far points {v}).card≤4) ∧
    (∀ v ∈ points, (far lines {v}).card≤4) := by decide +kernel

private theorem mixedBound (P Q A B : Finset V) (ap : A ⊆ P) (bq : B ⊆ Q)
    (trip : ∀ T ∈ P.powersetCard 3, (far Q T).card≤1)
    (one : ∀ v ∈ Q, (far P {v}).card≤4) (apart : ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v)
    (six : A.card+B.card=6) (big : 3≤A.card) : B=∅ := by
  obtain ⟨T,ta,three⟩ := exists_subset_card_eq big
  have small := trip T (mem_powersetCard.mpr ⟨ta.trans ap,three⟩)
  have cover : B ⊆ far Q T := fun v hv => mem_filter.mpr ⟨bq hv,fun u hu => apart u (ta hu) v hv⟩
  have le := card_le_card cover
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have avoid : A ⊆ far P {v} := by
    intro u hu
    refine mem_filter.mpr ⟨ap hu,?_⟩
    intro t ht
    obtain rfl := mem_singleton.mp ht
    exact fun e => apart u hu t hv e.symm
  have four := one v (bq hv)
  have := card_le_card avoid
  omega

private theorem sideProof :
    (∀ C ∈ points.powersetCard 6, ∃ v : V, G.edgeFinset \ incident C = star v) ∧
    (∀ C ∈ lines.powersetCard 6, ∃ v : V, G.edgeFinset \ incident C = star v) := by
  set_option maxRecDepth 10000 in decide +kernel

private theorem sixCenters (C : Finset V) (sz : C.card=6) (full : (incident C).card=18) :
    ∃ v : V, G.edgeFinset \ incident C = star v := by
  have apart (u) (hu : u ∈ C) (v) (hv : v ∈ C) (adj : G.Adj u v) : False := by
    have hv' : v ∈ C.erase u := mem_erase.mpr ⟨adj.ne.symm,hv⟩
    let D := (C.erase u).erase v
    have four : D.card=4 := by simp [D,card_erase_of_mem hv',card_erase_of_mem hu,sz]
    have rep : insert u (insert v D)=C := by rw [show insert v D=C.erase u from insert_erase hv',insert_erase hu]
    have eq : incident C = (star u ∪ star v) ∪ incident D := by
      conv_lhs => rw [← rep]
      simp only [incident,biUnion_insert,union_assoc]
    have contained : s(u,v) ∈ star u ∩ star v := mem_inter.mpr
      ⟨mem_image.mpr ⟨v,List.mem_toFinset.mpr adj,rfl⟩,
       mem_image.mpr ⟨u,List.mem_toFinset.mpr adj.symm,Sym2.eq_swap⟩⟩
    have overlap := card_pos.mpr (show (star u ∩ star v).Nonempty from ⟨_,contained⟩)
    have joint := card_union_add_card_inter (star u) (star v)
    rw [degree3,degree3] at joint
    have bound := card_union_le (star u ∪ star v) (incident D)
    have cap := incidentCap D
    rw [eq] at full
    omega
  let A := C ∩ points
  let B := C ∩ lines
  have sides : points ∪ lines=univ ∧ Disjoint points lines := by decide +kernel
  have all : A ∪ B=C := by simp only [A,B,← inter_union_distrib_left,sides.1,inter_univ]
  have disj : Disjoint A B := sides.2.mono inter_subset_right inter_subset_right
  have sum : A.card+B.card=6 := by rw [← card_union_of_disjoint disj,all,sz]
  have joined := fun u (hu : u ∈ A) v (hv : v ∈ B) => apart u (mem_inter.mp hu).1 v (mem_inter.mp hv).1
  by_cases big : 3≤A.card
  · have empty := mixedBound points lines A B inter_subset_right inter_subset_right triples.1 singles.1 joined sum big
    rw [empty,union_empty] at all
    exact sideProof.1 C (mem_powersetCard.mpr ⟨all ▸ inter_subset_right,sz⟩)
  · have empty := mixedBound lines points B A inter_subset_right inter_subset_right triples.2 singles.2
      (fun v hv u hu e => joined u hu v hv e.symm) (by omega) (by omega)
    rw [empty,empty_union] at all
    exact sideProof.2 C (mem_powersetCard.mpr ⟨all ▸ inter_subset_right,sz⟩)

/-- Six clean products that survive on eighteen edges leave exactly the three
edges incident to one vertex. Arbitrary wiring and either Fano orientation are allowed. -/
theorem missingStar {w : Wire 14} (sound : ∀ z, accepts w z → predicate z)
    (six : w.jobs.card=6) (edges18 : (survivors w).card=18) :
    ∃ v : V, G.edgeFinset \ survivors w = star v := by
  have clean := (describe sound).2
  have girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length := fun v p h => by
    have := girth_six v p h
    omega
  have square : NoSquare G := by
    intro i j a b ij ia ja ib jb
    by_contra ab
    exact noSquare G girth ia ja.symm jb ib.symm ij ab
  let side (p : Product 14) := if p.1.card≤1 then p.1 else p.2
  have tiny (p) (hp : p ∈ w.jobs) : (side p).card ≤ 1 := by
    by_cases h : p.1.card≤1
    · simp [side,h]
    · obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge h)
      rw [show side p=p.2 by simp [side,h]]
      exact card_le_one.mpr (fun a ha b hb => square x y a b ne
        (clean p hp x hx a ha) (clean p hp y hy a ha) (clean p hp x hx b hb) (clean p hp y hy b hb))
  let C := w.jobs.biUnion side
  have cmax : C.card≤6 := calc
    C.card ≤ ∑ p ∈ w.jobs, (side p).card := card_biUnion_le
    _ ≤ ∑ _ ∈ w.jobs, 1 := sum_le_sum tiny
    _ = 6 := by simp [six]
  have cap := incidentCap C
  have sub : survivors w ⊆ incident C := by
    intro e he
    obtain ⟨p,hp,u,hu,v,hv,rfl⟩ := (in_survivors _ _).mp he
    have adj := clean p hp u hu v hv
    by_cases h : p.1.card≤1
    · have center : u ∈ C := mem_biUnion.mpr ⟨p,hp,by simpa [side,h] using hu⟩
      exact mem_biUnion.mpr ⟨u,center,mem_image.mpr ⟨v,List.mem_toFinset.mpr adj,rfl⟩⟩
    · have center : v ∈ C := mem_biUnion.mpr ⟨p,hp,by simpa [side,h] using hv⟩
      exact mem_biUnion.mpr ⟨v,center,mem_image.mpr ⟨u,List.mem_toFinset.mpr adj.symm,Sym2.eq_swap⟩⟩
  have size := card_le_card sub
  have same := eq_of_subset_of_card_le sub (by omega)
  rw [same] at edges18 ⊢
  exact sixCenters C (by omega) edges18

/-- At the minimum possible loss, the three missing edges meet at one vertex.
All 26 gates are used and there is exactly one AND with an AND ancestor. -/
theorem threeLost (qs : List ℕ) (packed : Posted.output qs=2097151) (short : qs.length≤26) :
    let s := run 14 (qs.map Posted.decode)
    let w := s.wires.getD (13+qs.length) default
    missed w=3 → qs.length=26 ∧ s.dropped=1 ∧ w.jobs.card=6 ∧ s.bottom.length=12 ∧
      s.top.length=6 ∧ s.products.length+s.bypass=7 ∧ ∃ v : V, G.edgeFinset \ survivors w = star v := by
  let gs := qs.map Posted.decode
  let s := run 14 gs
  let w := s.wires.getD (13+qs.length) default
  have sem := Posted.semantics qs packed
  have valid := (run_valid 14 gs).1
  have structureBound := (nestedNecessary gs _ sem (by simpa [gs] using short)).2.2.2.2
  change missed w=3 → qs.length=26 ∧ s.dropped=1 ∧ w.jobs.card=6 ∧ s.bottom.length=12 ∧
    s.top.length=6 ∧ s.products.length+s.bypass=7 ∧ ∃ v : V, G.edgeFinset \ survivors w=star v
  intro three
  obtain ⟨len,one,six,bot,top,total⟩ := structureBound three
  have sub : survivors w ⊆ G.edgeFinset := (budget valid _ sem).sub
  have tally : G.edgeFinset.card=21 := by decide +kernel
  rw [missed,card_sdiff_of_subset sub,tally] at three
  have size : (survivors w).card=18 := by omega
  refine ⟨by simpa [gs] using len,one,six,bot,top,total,missingStar ?_ six size⟩
  exact fun z h => (sem z).mp ((port valid _).sound z h)

#print axioms missingStar
#print axioms threeLost
end Checkpoint122.Pruning
