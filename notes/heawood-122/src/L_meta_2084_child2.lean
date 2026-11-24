import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Paths

open Finset SimpleGraph
namespace PEqualNP.Outside.L_meta_2084_child2_aux

variable {V : Type*} [DecidableEq V]

/-- A source is empty or a singleton. A nonsingleton operand must have an earlier gate. -/
def Ready (previous : List (Finset V)) (s : Finset V) : Prop := s.card ≤ 1 ∨ s ∈ previous

/-- Binary union gates, most recent first. -/
def Built : List (Finset V) → Prop
  | [] => True
  | a :: gs => Built gs ∧ ∃ b c, a = b ∪ c ∧ Ready gs b ∧ Ready gs c

def charge (u : Finset V) : List (Finset V) → ℕ
  | [] => 0
  | a :: gs => (if 1 < a.card ∧ a ⊆ u then 1 else 0) + charge u gs

/-- Distinct leaves covered by several roots cost one gate per additional leaf.
Only nonsingleton union gates contained in the covered set are charged. -/
theorem cover (gs : List (Finset V)) (ok : Built gs) (r : Finset (Finset V))
    (u : Finset V) (hr : ∀ a ∈ r, Ready gs a) (hu : r.biUnion id = u) :
    u.card ≤ r.card + charge u gs := by
  induction gs generalizing r u with
  | nil =>
    change u.card ≤ r.card + 0
    rw [← hu, Nat.add_zero]
    calc
      (r.biUnion id).card ≤ ∑ a ∈ r, a.card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ r, 1 := Finset.sum_le_sum fun a ha => (hr a ha).resolve_right (by simp)
      _ = r.card := by simp
  | cons a gs ih =>
    obtain ⟨good,b,c,hbc,hb,hc⟩ := ok
    by_cases used : a ∈ r ∧ 1 < a.card
    · let r' := insert b (insert c (r.erase a))
      have hready : ∀ x ∈ r', Ready gs x := by
        intro x hx
        simp only [r',mem_insert,mem_erase] at hx
        rcases hx with rfl | rfl | ⟨ne,mem⟩
        · exact hb
        · exact hc
        · rcases hr _ mem with small | seen
          · exact Or.inl small
          · exact Or.inr ((List.mem_cons.mp seen).resolve_left ne)
      have hu' : r'.biUnion id = u := by
        rw [← hu]
        ext x
        simp only [mem_biUnion,id_eq,r',mem_insert,mem_erase]
        constructor
        · rintro ⟨s,rfl | rfl | ⟨_,hs⟩,hx⟩
          · exact ⟨a,used.1,hbc ▸ mem_union_left _ hx⟩
          · exact ⟨a,used.1,hbc ▸ mem_union_right _ hx⟩
          · exact ⟨s,hs,hx⟩
        · rintro ⟨s,hs,hx⟩
          by_cases eqn : s = a
          · subst s
            rw [hbc,mem_union] at hx
            exact hx.elim (fun h => ⟨b,Or.inl rfl,h⟩) (fun h => ⟨c,Or.inr (Or.inl rfl),h⟩)
          · exact ⟨s,Or.inr (Or.inr ⟨eqn,hs⟩),hx⟩
      have more : r'.card ≤ r.card + 1 := by
        have h1 := Finset.card_insert_le b (insert c (r.erase a))
        have h2 := Finset.card_insert_le c (r.erase a)
        have h3 := Finset.card_erase_add_one used.1
        unfold r'
        omega
      have huA : a ⊆ u := by
        intro x hx
        rw [← hu,mem_biUnion]
        exact ⟨a,used.1,hx⟩
      have bound := ih good r' u hready hu'
      simp only [charge,used.2,huA,and_self,ite_true]
      omega
    · have prev : ∀ x ∈ r, Ready gs x := by
        intro x hx
        rcases hr x hx with small | seen
        · exact Or.inl small
        · rcases List.mem_cons.mp seen with rfl | mem
          · exact Or.inl (by by_contra! big; exact used ⟨hx,big⟩)
          · exact Or.inr mem
      have bound := ih good r u prev hu
      rw [charge]
      omega

/-- Sets that meet pairwise in at most one vertex cannot share a nonsingleton gate charge. -/
theorem sumCharge {I : Type*} [DecidableEq I] (centers : Finset I) (u : I → Finset V)
    (sep : ∀ i ∈ centers, ∀ j ∈ centers, i ≠ j → ((u i) ∩ (u j)).card ≤ 1)
    (gs : List (Finset V)) : (∑ i ∈ centers, charge (u i) gs) ≤ gs.length := by
  induction gs with
  | nil => simp [charge]
  | cons a gs ih =>
    have once : (centers.filter fun i => 1 < a.card ∧ a ⊆ u i).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨hi,big,ai⟩ := mem_filter.mp hi
      obtain ⟨hj,_,aj⟩ := mem_filter.mp hj
      by_contra e
      have l := card_le_card (Finset.subset_inter ai aj)
      have h := sep i hi j hj e
      omega
    simp only [charge,Finset.sum_add_distrib,List.length_cons]
    simpa using Nat.add_le_add once ih |>.trans_eq (Nat.add_comm 1 gs.length)

theorem totalLeaves {I : Type*} [DecidableEq I] (centers : Finset I) (u : I → Finset V)
    (sep : ∀ i ∈ centers, ∀ j ∈ centers, i ≠ j → ((u i) ∩ (u j)).card ≤ 1)
    (gs : List (Finset V)) (ok : Built gs) (r : I → Finset (Finset V))
    (hr : ∀ i ∈ centers, ∀ a ∈ r i, Ready gs a)
    (hu : ∀ i ∈ centers, (r i).biUnion id = u i) :
    (∑ i ∈ centers, (u i).card) ≤ (∑ i ∈ centers, (r i).card) + gs.length := by
  calc
    _ ≤ ∑ i ∈ centers, ((r i).card + charge (u i) gs) :=
      sum_le_sum fun i hi => cover gs ok (r i) (u i) (hr i hi) (hu i hi)
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left (sumCharge centers u sep gs) _

/-- No two distinct vertices have two common neighbors. -/
def NoSquare (G : SimpleGraph V) : Prop :=
  ∀ i j a b, i ≠ j → G.Adj i a → G.Adj j a → G.Adj i b → G.Adj j b → a = b

/-- A family of stars in a square-free graph may share the union circuit
constructing their leaves. The graph's distinct covered edges still cost one
union gate or one star per edge. A center may have several separate stars. -/
theorem starEdges {I : Type*} [DecidableEq I] (G : SimpleGraph V) (square : NoSquare G)
    (gs : List (Finset V)) (ok : Built gs) (jobs : Finset I) (center : I → V)
    (leaf : I → Finset V) (ready : ∀ j ∈ jobs, Ready gs (leaf j))
    (sound : ∀ j ∈ jobs, ∀ v ∈ leaf j, G.Adj (center j) v)
    (E : Finset (Sym2 V)) (covered : ∀ e ∈ E, ∃ j ∈ jobs, ∃ v ∈ leaf j, e = s(center j,v)) :
    E.card ≤ jobs.card + gs.length := by
  classical
  let cs := jobs.image center
  let r := fun c => (jobs.filter fun j => center j = c).image leaf
  let u := fun c => (r c).biUnion id
  have adj {c v} (hv : v ∈ u c) : G.Adj c v := by
    obtain ⟨b,hb,hvb⟩ := (show ∃ b ∈ r c, v ∈ b from mem_biUnion.mp hv)
    obtain ⟨j,hj,eqn⟩ := mem_image.mp hb
    rw [← (mem_filter.mp hj).2]
    exact sound j (mem_filter.mp hj).1 v (eqn ▸ hvb)
  have sep : ∀ i ∈ cs, ∀ j ∈ cs, i ≠ j → ((u i) ∩ (u j)).card ≤ 1 := by
    intro i _ j _ ne
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨ai,aj⟩ := mem_inter.mp ha
    obtain ⟨bi,bj⟩ := mem_inter.mp hb
    exact square i j a b ne (adj ai) (adj aj) (adj bi) (adj bj)
  have rr : ∀ i ∈ cs, ∀ a ∈ r i, Ready gs a := by
    intro i _ a ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    exact ready _ (mem_filter.mp hj).1
  have reach := totalLeaves cs u sep gs ok r rr (fun _ _ => rfl)
  have roots : (∑ i ∈ cs, (r i).card) ≤ jobs.card := by
    rw [card_eq_sum_card_image center jobs]
    exact sum_le_sum fun _ _ => card_image_le
  let outputs := fun c => (u c).image (fun v => s(c,v))
  have inc : E ⊆ cs.biUnion outputs := by
    intro e he
    obtain ⟨j,hj,v,hv,rfl⟩ := covered e he
    apply mem_biUnion.mpr
    refine ⟨center j,mem_image_of_mem _ hj,mem_image.mpr ⟨v,?_,rfl⟩⟩
    exact mem_biUnion.mpr ⟨leaf j,mem_image_of_mem _ (mem_filter.mpr ⟨hj,rfl⟩),hv⟩
  calc
    E.card ≤ (cs.biUnion outputs).card := card_le_card inc
    _ ≤ ∑ c ∈ cs, (outputs c).card := card_biUnion_le
    _ ≤ ∑ c ∈ cs, (u c).card := sum_le_sum fun _ _ => card_image_le
    _ ≤ _ := reach.trans (Nat.add_le_add_right roots _)

/-- A sound, nonempty rectangle in a square-free graph is a star. Its leaves
are one of the two original operands of the product gate. -/
theorem rectangleStar (G : SimpleGraph V) (sq : NoSquare G) (a b : Finset V)
    (ha : a.Nonempty) (hb : b.Nonempty) (sound : ∀ p ∈ a, ∀ q ∈ b, G.Adj p q) :
    ∃ c leaf, (leaf = a ∨ leaf = b) ∧ (∀ v ∈ leaf, G.Adj c v) ∧
      ∀ p ∈ a, ∀ q ∈ b, ∃ v ∈ leaf, s(p,q) = s(c,v) := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hb
  by_cases single : ∀ i ∈ a, i = p
  · exact ⟨p,b,Or.inr rfl,sound p hp,fun i hi j hj => ⟨j,hj,by rw [single i hi]⟩⟩
  · push Not at single
    obtain ⟨p',hp',ne⟩ := single
    have other (j) (hj : j ∈ b) : j = q :=
      sq p' p j q ne (sound p' hp' j hj) (sound p hp j hj) (sound p' hp' q hq) (sound p hp q hq)
    refine ⟨q,a,Or.inl rfl,fun v hv => (sound v hv q hq).symm,?_⟩
    intro i hi j hj
    exact ⟨i,hi,by rw [other j hj,Sym2.eq_swap]⟩

/-- A binary union DAG supplies the two sides of each product. If every
product rectangle is clean, the covered edge count is bounded by the total
number of union and product gates, even with arbitrary fanout. -/
theorem rectangleEdges {I : Type*} [DecidableEq I] (G : SimpleGraph V) (square : NoSquare G)
    (gs : List (Finset V)) (ok : Built gs) (jobs : Finset I) (a b : I → Finset V)
    (readA : ∀ j ∈ jobs, Ready gs (a j)) (readB : ∀ j ∈ jobs, Ready gs (b j))
    (sound : ∀ j ∈ jobs, ∀ u ∈ a j, ∀ v ∈ b j, G.Adj u v)
    (E : Finset (Sym2 V))
    (covered : ∀ e ∈ E, ∃ j ∈ jobs, ∃ u ∈ a j, ∃ v ∈ b j, e = s(u,v)) :
    E.card ≤ jobs.card + gs.length := by
  classical
  let active := jobs.filter fun j => (a j).Nonempty ∧ (b j).Nonempty
  let ids : Finset {i // i ∈ active} := Finset.univ
  have star (j : {i // i ∈ active}) := rectangleStar G square (a j) (b j)
    (mem_filter.mp j.2).2.1 (mem_filter.mp j.2).2.2 (sound j (mem_filter.mp j.2).1)
  choose center leaf sides clean wins using star
  have ready (j : {i // i ∈ active}) : Ready gs (leaf j) := by
    rcases sides j with ha | hb
    · rw [ha]; exact readA j (mem_filter.mp j.2).1
    · rw [hb]; exact readB j (mem_filter.mp j.2).1
  have covers (e) (he : e ∈ E) :
      ∃ j ∈ ids, ∃ v ∈ leaf j, e = s(center j,v) := by
    obtain ⟨i,hi,v,hv,w,hw,rfl⟩ := covered e he
    let j : {k // k ∈ active} := ⟨i,mem_filter.mpr ⟨hi,⟨v,hv⟩,⟨w,hw⟩⟩⟩
    exact ⟨j,mem_univ _,wins j v hv w hw⟩
  have h := starEdges G square gs ok ids center leaf (fun j _ => ready j) (fun j _ => clean j) E covers
  have le : ids.card ≤ jobs.card := by
    simpa [ids] using (Finset.card_filter_le (s := jobs) (p := fun j => (a j).Nonempty ∧ (b j).Nonempty))
  exact h.trans (Nat.add_le_add_right le _)


theorem noSquare {n : ℕ} (G : SimpleGraph (Fin n))
    (girth : ∀ z (p : G.Walk z z), p.IsCycle → 5 ≤ p.length)
    {i j k l : Fin n} (ij : G.Adj i j) (jk : G.Adj j k)
    (kl : G.Adj k l) (li : G.Adj l i) (ik : i ≠ k) (jl : j ≠ l) : False := by
  let p : G.Walk i i := .cons ij (.cons jk (.cons kl (.cons li .nil)))
  have cyc : p.IsCycle := by
    refine Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [p]⟩
    simp [p, Walk.tail_cons, ij.ne.symm, jk.ne, kl.ne, li.ne, ik.symm, jl]
  have too := girth i p cyc
  change 5 ≤ 4 at too
  omega


def coverTruth {n m : ℕ} (X Y : Fin m → Finset (Fin n)) (z : Fin n → Bool) : Prop :=
  ∃ i, (∃ u ∈ X i, z u = true) ∧ (∃ v ∈ Y i, z v = true)

/-- Truth on singleton and two-vertex inputs recovers cleanliness and coverage
for a positive formula that computes the edge function. -/
theorem cleanCoverOfSemantics {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Y : Fin m → Finset (Fin n))
    (computes : ∀ z, coverTruth X Y z ↔
      ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) :
    (∀ i u, u ∈ X i → ∀ v, v ∈ Y i → G.Adj u v) ∧
    (∀ e ∈ G.edgeFinset, ∃ i u v, u ∈ X i ∧ v ∈ Y i ∧ e = s(u,v)) := by
  classical
  let pair (u v w : Fin n) := decide (w = u ∨ w = v)
  have pairTrue (u v w : Fin n) : pair u v w = true ↔ w = u ∨ w = v := by simp [pair]
  have clean (i : Fin m) (u : Fin n) (hu : u ∈ X i) (v : Fin n) (hv : v ∈ Y i) :
      G.Adj u v := by
    have yes : coverTruth X Y (pair u v) :=
      ⟨i,⟨u,hu,(pairTrue u v u).mpr (Or.inl rfl)⟩,⟨v,hv,(pairTrue u v v).mpr (Or.inr rfl)⟩⟩
    obtain ⟨a,b,ab,ha,hb⟩ := (computes _).mp yes
    rcases (pairTrue u v a).mp ha with rfl | rfl <;>
      rcases (pairTrue _ _ b).mp hb with rfl | rfl
    · exact False.elim (G.irrefl ab)
    · exact ab
    · exact ab.symm
    · exact False.elim (G.irrefl ab)
  refine ⟨clean,?_⟩
  intro e
  refine Sym2.ind (fun u v => ?_) e
  intro h
  rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at h
  have yes := (computes (pair u v)).mpr
    ⟨u,v,h,(pairTrue u v u).mpr (Or.inl rfl),(pairTrue u v v).mpr (Or.inr rfl)⟩
  obtain ⟨i,⟨a,ha,pa⟩,⟨b,hb,pb⟩⟩ := yes
  refine ⟨i,a,b,ha,hb,?_⟩
  have ne := (clean i a ha b hb).ne
  rcases (pairTrue u v a).mp pa with rfl | rfl <;>
    rcases (pairTrue _ _ b).mp pb with rfl | rfl
  · exact False.elim (ne rfl)
  · rfl
  · exact Sym2.eq_swap
  · exact False.elim (ne rfl)

/-- Read the reverse topological list one gate at a time, including duplicate gates. -/
theorem builtOfSchedule {n : ℕ} (B : List (Finset (Fin n)))
    (sched : ∀ P a T, B = P ++ a :: T →
      ∃ b c, a = b ∪ c ∧ Ready T b ∧ Ready T c) : Built B := by
  induction B with
  | nil => trivial
  | cons a B ih =>
    refine ⟨ih (fun P v T eqn => sched (a :: P) v T (by simp [eqn])), ?_⟩
    exact sched [] a B rfl

/-- One side of each clean rectangle supplies at most one vertex to the cover.
The sharing bound for binary unions pays for all edges across the rectangles. -/
theorem price {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (B : List (Finset (Fin n))) (X Y : Fin m → Finset (Fin n)) (good : Built B)
    (ready : ∀ i, Ready B (X i) ∧ Ready B (Y i))
    (truth : ∀ z, coverTruth X Y z ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) :
    ∃ V : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ V ∨ v ∈ V) ∧
      G.edgeSet.ncard + V.card ≤ B.length + 2*m := by
  classical
  obtain ⟨clean,cover⟩ := cleanCoverOfSemantics G X Y truth
  have square : NoSquare G := by
    intro i j a b ij ia ja ib jb
    by_contra ab
    exact noSquare G girth ia ja.symm jb ib.symm ij ab
  let side (i : Fin m) := if (X i).card ≤ 1 then X i else Y i
  have small (i : Fin m) : (side i).card ≤ 1 := by
    by_cases h : (X i).card ≤ 1
    · simp [side,h]
    · obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge h)
      rw [show side i = Y i by simp [side,h]]
      apply card_le_one.mpr
      intro a ha b hb
      exact square x y a b ne (clean i x hx a ha) (clean i y hy a ha)
        (clean i x hx b hb) (clean i y hy b hb)
  let V := (univ : Finset (Fin m)).biUnion side
  have vCard : V.card ≤ m := calc
    V.card ≤ ∑ i, (side i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin m, 1 := sum_le_sum fun i _ => small i
    _ = m := by simp
  have eCard := rectangleEdges G square B good (univ : Finset (Fin m)) X Y
    (fun i _ => (ready i).1) (fun i _ => (ready i).2) (fun i _ => clean i) G.edgeFinset
    (by
      intro e he
      obtain ⟨i,u,v,hu,hv,eqn⟩ := cover e he
      exact ⟨i,mem_univ _,u,hu,v,hv,eqn⟩)
  have bound : G.edgeSet.ncard ≤ m + B.length := by
    simpa only [← G.coe_edgeFinset, Set.ncard_coe_finset, card_univ, Fintype.card_fin] using eCard
  refine ⟨V,?_,by omega⟩
  intro u v huv
  obtain ⟨i,a,b,ha,hb,e⟩ := cover s(u,v) (by simpa using huv)
  have here : a ∈ V ∨ b ∈ V := by
    by_cases h : (X i).card ≤ 1
    · exact Or.inl (mem_biUnion.mpr ⟨i,mem_univ _,by simpa [side,h] using ha⟩)
    · exact Or.inr (mem_biUnion.mpr ⟨i,mem_univ _,by simpa [side,h] using hb⟩)
  rw [Sym2.eq_iff] at e
  rcases e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact here
  · exact here.symm

end PEqualNP.Outside.L_meta_2084_child2_aux

theorem PEqualNP.Outside.L_meta_2084_child2 :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → ∀ (x5 : List (Finset (Fin x1))) (x6 : ℕ) (x7 x8 : Fin x6 → Finset (Fin x1)), (∀ (x9 : List (Finset (Fin x1))) (x10 : Finset (Fin x1)) (x11 : List (Finset (Fin x1))), x5 = x9 ++ x10 :: x11 → ∃ (x13 : Finset (Fin x1)) (x14 : Finset (Fin x1)), x10 = x13 ∪ x14 ∧ (x13.card ≤ (1 : ℕ) ∨ x13 ∈ x11) ∧ (x14.card ≤ (1 : ℕ) ∨ x14 ∈ x11)) → (∀ (x10 : Fin x6), ((x7 x10).card ≤ (1 : ℕ) ∨ x7 x10 ∈ x5) ∧ ((x8 x10).card ≤ (1 : ℕ) ∨ x8 x10 ∈ x5)) → (∀ (x11 : Fin x1 → Bool), (∃ (x12 : Fin x6), (∃ x13 ∈ x7 x12, x11 x13 = Bool.true) ∧ ∃ x13 ∈ x8 x12, x11 x13 = Bool.true) ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∃ (x12 : Finset (Fin x1)), (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → x13 ∈ x12 ∨ x14 ∈ x12) ∧ x2.edgeSet.ncard + x12.card ≤ x5.length + (2 : ℕ) * x6 := by
  intro n G _ girth B m X Y sched ready truth
  exact PEqualNP.Outside.L_meta_2084_child2_aux.price G girth B X Y (PEqualNP.Outside.L_meta_2084_child2_aux.builtOfSchedule B sched) ready truth
