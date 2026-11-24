import PrunedProgram
import HeawoodStages

namespace Checkpoint122.Pruning
open Finset StarUnion SimpleGraph
open PEqualNP.Outside.L_meta_3004_aux.Controls
open PEqualNP.Outside.L_meta_2268_aux.Normal

def pair (u v t : V) := decide (t = u ∨ t = v)
private theorem pairTrue (u v t : V) : pair u v t = true ↔ t = u ∨ t = v := by simp [pair]

def part (p : Product 14) := (p.1 ×ˢ p.2).image (fun q => s(q.1,q.2))
def survivors (w : Wire 14) := w.jobs.biUnion part

theorem describe {w : Wire 14}
    (sound : ∀ z, accepts w z → predicate z) :
    w.raw=∅ ∧ (∀ p ∈ w.jobs, ∀ u ∈ p.1, ∀ v ∈ p.2, G.Adj u v) := by
  have valid z h := (orientation z).mp (sound z h)
  constructor
  · apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨a,b,ab,ha,hb⟩ := valid (fun t => decide (t=u))
      (Or.inl ⟨u,hu,by simp⟩)
    simp only [decide_eq_true_eq] at ha hb
    exact ab.ne (ha.trans hb.symm)
  · intro p hp u hu v hv
    obtain ⟨a,b,ab,ha,hb⟩ := valid (pair u v) (Or.inr ⟨p,hp,⟨u,hu,by simp [pair]⟩,⟨v,hv,by simp [pair]⟩⟩)
    rcases (pairTrue _ _ _).mp ha with rfl|rfl <;> rcases (pairTrue _ _ _).mp hb with rfl|rfl
    · exact False.elim (G.irrefl ab)
    · exact ab
    · exact ab.symm
    · exact False.elim (G.irrefl ab)

theorem in_survivors (w : Wire 14) (e) :
    e ∈ survivors w ↔ ∃ p ∈ w.jobs, ∃ u ∈ p.1, ∃ v ∈ p.2, e = s(u,v) := by
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := mem_biUnion.mp h
    obtain ⟨⟨u,v⟩,hr,h⟩ := mem_image.mp he
    exact ⟨p,hp,u,(mem_product.mp hr).1,v,(mem_product.mp hr).2,h.symm⟩
  · rintro ⟨p,hp,u,hu,v,hv,rfl⟩
    exact mem_biUnion.mpr ⟨p,hp,mem_image.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩

/-- Membership counts actual two-vertex assignments that still reach the selected output. -/
theorem survives_iff {w : Wire 14} (sound : ∀ z, accepts w z → predicate z) (u v : V) :
    s(u,v) ∈ survivors w ↔ accepts w (pair u v) := by
  obtain ⟨raw,clean⟩ := describe sound
  rw [in_survivors]
  constructor
  · rintro ⟨p,hp,a,ha,b,hb,eq⟩
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      exact Or.inr ⟨p,hp,⟨_,ha,by simp [pair]⟩,⟨_,hb,by simp [pair]⟩⟩
  · rintro (h|⟨p,hp,⟨a,ha,pa⟩,⟨b,hb,pb⟩⟩)
    · simp [lit,raw] at h
    · refine ⟨p,hp,a,ha,b,hb,?_⟩
      have ne := (clean p hp a ha b hb).ne
      rcases (pairTrue _ _ _).mp pa with rfl|rfl <;> rcases (pairTrue _ _ _).mp pb with rfl|rfl
      · exact False.elim (ne rfl)
      · rfl
      · exact Sym2.eq_swap
      · exact False.elim (ne rfl)

structure Budget (s : State 14) (w : Wire 14) : Prop where
  sub : survivors w ⊆ G.edgeFinset
  bottom : (survivors w).card ≤ w.jobs.card + s.bottom.length
  cubic : (survivors w).card ≤ 3*w.jobs.card
  products : w.jobs.card ≤ s.products.length
  top : w.tags.card ≤ s.top.length+1
  intact : none ∉ w.tags → survivors w=G.edgeFinset

theorem budget {s : State 14} (hs : Valid s) (out : ℕ)
    (spec : ∀ z, (s.wires.getD out default).full z = true ↔ predicate z) :
    Budget s (s.wires.getD out default) := by
  let w := s.wires.getD out default
  have f := port hs out
  have sound z (h : accepts w z) := (spec z).mp (f.sound z h)
  have clean := (describe sound).2
  have sub : survivors w ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨p,hp,u,hu,v,hv,rfl⟩ := (in_survivors w _).mp he
    simpa using (clean p hp u hu v hv)
  have girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length := fun v p h => by
    have := girth_six v p h
    omega
  have square : NoSquare G := by
    intro i j a b ij ia ja ib jb
    by_contra ab
    exact noSquare G girth ia ja.symm jb ib.symm ij ab
  have cost := rectangleEdges G square s.bottom hs.bottom w.jobs Prod.fst Prod.snd
    (fun p hp => (hs.operands p (f.owned p hp)).1) (fun p hp => (hs.operands p (f.owned p hp)).2)
    clean (survivors w) (fun e he => (in_survivors w e).mp he)
  have reg : ∀ v ∉ (∅ : Finset V), (G.neighborSet v).ncard=3 := by intro v _; rw [G.ncard_neighborSet,cubic]
  have cap (p) (hp : p ∈ w.jobs) : (part p).card ≤ 3 := by
    have h := (cleanProductCount G ∅ reg (by simp) girth p.1 p.2 (clean p hp)).1
    exact (card_image_le.trans ((card_product p.1 p.2).le.trans h))
  refine ⟨sub,cost,?_,?_,collectorBound _ hs.top _ f.high,?_⟩
  · calc (survivors w).card ≤ ∑ p ∈ w.jobs, (part p).card := card_biUnion_le
         _ ≤ ∑ _p ∈ w.jobs, 3 := sum_le_sum cap
         _ = 3*w.jobs.card := by simp [Nat.mul_comm]
  · exact (card_le_card (t := s.products.toFinset) (fun p hp => List.mem_toFinset.mpr (f.owned p hp))).trans
      s.products.toFinset_card_le
  · intro no
    apply Subset.antisymm sub
    intro e
    refine Sym2.ind (fun u v => ?_) e
    intro h
    have adj : G.Adj u v := by simpa using h
    apply (survives_iff sound u v).mpr
    apply f.same no
    apply (spec _).mpr
    exact (orientation _).mpr ⟨u,v,adj,by simp [pair],by simp [pair]⟩

def missed (w : Wire 14) := (G.edgeFinset \ survivors w).card

/-- Suppressing all nested AND gates loses at least three distinct positive edge
assignments for every Heawood circuit of size at most 26. The number of losses
also bounds the number of nested gates, including unused ones. -/
theorem nestedNecessary (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z = true ↔ predicate z)
    (short : gs.length ≤ 26) :
    let s := run 14 gs
    let w := s.wires.getD out default
    none ∈ w.tags ∧ 1 ≤ s.dropped ∧ 3 ≤ missed w ∧ 3*(s.dropped+3) ≤ 4*missed w ∧
      (missed w=3 → gs.length=26 ∧ s.dropped=1 ∧ w.jobs.card=6 ∧ s.bottom.length=12 ∧
        s.top.length=6 ∧ s.products.length+s.bypass=7) := by
  let s := run 14 gs
  let w := s.wires.getD out default
  obtain ⟨valid,length⟩ := run_valid 14 gs
  obtain ⟨sub,low,cu,pr,top,intact⟩ := budget valid out spec
  change s.bottom.length+s.top.length+s.products.length+s.dropped+s.bypass=gs.length at length
  change survivors w ⊆ G.edgeFinset at sub
  change (survivors w).card ≤ w.jobs.card+s.bottom.length at low
  change (survivors w).card ≤ 3*w.jobs.card at cu
  change w.jobs.card ≤ s.products.length at pr
  change w.tags.card ≤ s.top.length+1 at top
  have edges21 : G.edgeFinset.card=21 := by decide +kernel
  have loss : missed w + (survivors w).card = 21 := by
    rw [missed,card_sdiff_of_subset sub,edges21]
    have h := card_le_card sub
    omega
  have height : w.jobs.card ≤ w.tags.card := card_eraseNone_le _
  have mark : none ∈ w.tags := by
    by_contra h
    have eq : survivors w=G.edgeFinset := intact h
    rw [eq,edges21] at low cu
    omega
  have k : 0 < s.dropped := (port valid out).marked mark
  have tagCount : w.jobs.card = w.tags.card-1 := card_eraseNone_of_mem mark
  have positive : 0 < w.tags.card := card_pos.mpr ⟨none,mark⟩
  have lost : 0 < missed w := by omega
  have extra : w.jobs.card+1 ≤ s.products.length+s.bypass := by
    by_contra! small
    have zero : s.bypass=0 := by omega
    have f := port valid out
    have imp : w.pure=false := by
      cases hp : w.pure with
      | false => rfl
      | true =>
        have empty : w.tags=∅ := f.empty hp
        simp [empty] at mark
    have same : w.jobs=s.products.toFinset := by
      apply eq_of_subset_of_card_le (fun p hp => List.mem_toFinset.mpr (f.owned p hp))
      change s.products.toFinset.card ≤ w.jobs.card
      exact s.products.toFinset_card_le.trans (by omega)
    have every : G.edgeFinset ⊆ survivors w := by
      intro e
      refine Sym2.ind (fun u v => ?_) e
      intro h
      have yes := (spec (pair u v)).mpr ((orientation _).mpr
        ⟨u,v,by simpa using h,by simp [pair],by simp [pair]⟩)
      obtain ⟨p,hp,l,r⟩ := f.origin imp zero _ yes
      apply (survives_iff (fun z a => (spec z).mp (f.sound z a)) u v).mpr
      exact Or.inr ⟨p,same ▸ List.mem_toFinset.mpr hp,l,r⟩
    have hi := card_le_card every
    rw [edges21] at hi
    omega
  change none ∈ w.tags ∧ 1 ≤ s.dropped ∧ 3 ≤ missed w ∧ 3*(s.dropped+3) ≤ 4*missed w ∧
    (missed w=3 → gs.length=26 ∧ s.dropped=1 ∧ w.jobs.card=6 ∧ s.bottom.length=12 ∧
        s.top.length=6 ∧ s.products.length+s.bypass=7)
  exact ⟨mark,k,by omega,by omega,by omega⟩

#print axioms survives_iff
#print axioms budget
#print axioms nestedNecessary
end Checkpoint122.Pruning
