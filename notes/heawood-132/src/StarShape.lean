import StarBudget

namespace Checkpoint132.Star
open Finset Checkpoint122.Pruning Checkpoint124.Heawood Checkpoint125 Checkpoint125.Heawood
open Checkpoint125.Certificate Checkpoint127.Heawood Checkpoint128.Heawood Checkpoint129.Heawood
open PEqualNP.Outside.L_meta_3004_aux.Controls

def center : Support 14 := {6}
def tips : Support 14 := {8,9,11}
private theorem partHas (p : Product 14) (a b : V) :
    s(a,b)∈part p ↔ (a∈p.1 ∧ b∈p.2) ∨ (b∈p.1 ∧ a∈p.2) := by
  constructor
  · intro h
    obtain ⟨⟨u,v⟩,uv,eq⟩ := mem_image.mp h
    obtain ⟨hu,hv⟩ := mem_product.mp uv
    change s(u,v)=s(a,b) at eq
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl ⟨hu,hv⟩
    · exact Or.inr ⟨hu,hv⟩
  · rintro (⟨ha,hb⟩|⟨hb,ha⟩)
    · exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,rfl⟩
    · exact mem_image.mpr ⟨(b,a),mem_product.mpr ⟨hb,ha⟩,Sym2.eq_swap⟩

private theorem atCenter (b : Support 14) (x : V) : s(6,x)∈part (center,b) ↔ x∈b := by
  rw [partHas]
  simp only [center,mem_singleton,true_and]
  exact ⟨fun h => h.elim id (fun ⟨e,hb⟩ => e ▸ hb),Or.inl⟩

private theorem side {p : Product 14} (h : part p=part (center,tips)) :
    p=(center,tips) ∨ p=(tips,center) := by
  have first {a b : Support 14} (eq : part (a,b)=part (center,tips)) (hc : (6 : V)∈a) (ht : (8 : V)∈b) :
      (a,b)=(center,tips) := by
    have unique : ∀ v : V,s(v,8)∈part (center,tips) → v=6 := by decide +kernel
    have one : a=center := eq_singleton_iff_unique_mem.mpr ⟨hc,fun v hv =>
      unique v (eq ▸ (partHas (a,b) v 8).mpr (Or.inl ⟨hv,ht⟩))⟩
    subst a
    have other : b=tips := by
      ext x
      rw [←atCenter b x,←atCenter tips x,eq]
    rw [other]
  have member : s(6,8)∈part p := by rw [h]; decide +kernel
  rcases (partHas p 6 8).mp member with yes|no
  · exact Or.inl (first h yes.1 yes.2)
  · have swap : part (p.2,p.1)=part p := by
      ext x
      induction x using Sym2.inductionOn with
      | _ a b =>
        exact (partHas (p.2,p.1) a b).trans
          (Iff.trans ⟨fun h => h.elim (fun j => Or.inr j.symm) (fun j => Or.inl j.symm),
                      fun h => h.elim (fun j => Or.inr j.symm) (fun j => Or.inl j.symm)⟩
            (partHas p a b).symm)
    have eq := first (swap.trans h) no.2 no.1
    exact Or.inr (congrArg Prod.swap eq)

private theorem twoUnions {B : List (Support 14)} (built : StarUnion.Built B) (length : B.length=2)
    (ready : StarUnion.Ready B tips) : ∃ a,a.card=2 ∧ a⊆tips ∧ B=[tips,a] := by
  have big : tips.card=3 := by decide +kernel
  obtain ⟨h,q,rfl⟩ := List.exists_cons_of_ne_nil (l:=B) (by intro h; simp [h] at length)
  obtain ⟨a,q,rfl⟩ := List.exists_cons_of_ne_nil (l:=q) (by intro h; simp [h] at length)
  obtain rfl : q=[] := List.length_eq_zero_iff.mp (by simpa using length)
  obtain ⟨⟨_,u,v,eq₁,ru,rv⟩,b,c,eq₂,rb,rc⟩ := built
  have unit {d : Support 14} (r : StarUnion.Ready [] d) : d.card≤1 := r.resolve_right (by simp)
  have ab : a.card≤2 := eq₁ ▸ (card_union_le u v).trans (Nat.add_le_add (unit ru) (unit rv))
  have top : tips=h := by
    have mem := ready.resolve_left (by omega)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem.resolve_right (fun small => by rw [←small] at ab; omega)
  have unionEq := top.trans eq₂
  have bound := card_union_le b c
  rw [←unionEq] at bound
  have rb' : b.card≤1 ∨ b=a := rb.imp_right (by simp)
  have rc' : c.card≤1 ∨ c=a := rc.imp_right (by simp)
  have both (hb : b=a) (hc : c=a) : False := by
    rw [hb,hc,union_self] at unionEq
    rw [←unionEq] at ab
    omega
  refine ⟨a,?_,?_,by rw [top]⟩
  · rcases rb' with lb|hb <;> rcases rc' with lc|hc
    · omega
    · rw [hc] at bound; omega
    · rw [hb] at bound; omega
    · exact (both hb hc).elim
  · rw [unionEq]
    rcases rb' with lb|hb
    · rcases rc' with lc|hc
      · omega
      · exact hc ▸ subset_union_right
    · exact hb ▸ subset_union_left

/-- The sole 18-loss shape at equality must compute a pair of neighbors, their
three-way disjunction, and their product with the center. -/
theorem starGates (lower : RowFloor star 22) (gs : List Op) (out : ℕ)
    (spec : ∀ z,((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (eq : lost ((run 14 gs).wires.getD out default)=decoded star.shape.mask) (short : gs.length≤26) :
    let s := run 14 gs
    let w := s.wires.getD out default
    gs.length=26 ∧ (w.jobs={(center,tips)} ∨ w.jobs={(tips,center)}) ∧
      ∃ a,a.card=2 ∧ a⊆tips ∧ kept (survivors w) s.bottom=[tips,a] := by
  let s := run 14 gs
  let w := s.wires.getD out default
  have valid : Valid s := (run_valid 14 gs).1
  obtain ⟨size,num,p,jobs,rectangle⟩ := starEquality lower gs out spec eq short
  have sub := (budget valid out spec).sub
  have lostGraph := lostEdges w
  rw [eq] at lostGraph
  have footprint : G.edgeFinset \ (decoded star.shape.mask).image edge=part (center,tips) := by decide +kernel
  have exactEdges : survivors w=part (center,tips) := by
    rw [←footprint,lostGraph]
    ext x
    simp only [mem_sdiff]
    exact ⟨fun h => ⟨sub h,fun hx => hx.2 h⟩,fun h => Classical.byContradiction (fun ha => h.2 ⟨h.1,ha⟩)⟩
  have sides := side (rectangle.symm.trans exactEdges)
  have reg : Regular (survivors w) tips := by rw [exactEdges]; decide +kernel
  have hp : p∈w.jobs := by rw [jobs]; simp
  have operands := valid.operands p ((port valid out).owned p hp)
  have rt : StarUnion.Ready s.bottom tips := by
    rcases sides with h|h
    · rw [h] at operands; exact operands.2
    · rw [h] at operands; exact operands.1
  have rk : StarUnion.Ready (kept (survivors w) s.bottom) tips :=
    rt.imp_right (fun h => List.mem_filter.mpr ⟨h,decide_eq_true reg⟩)
  refine ⟨size,?_,twoUnions (keptBuilt _ valid.bottom) num rk⟩
  change w.jobs={(center,tips)} ∨ w.jobs={(tips,center)}
  rw [jobs]
  exact sides.imp (fun h => congrArg _ h) (fun h => congrArg _ h)

#print axioms starGates
end Checkpoint132.Star
