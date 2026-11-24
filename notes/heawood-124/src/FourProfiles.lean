import FourLost

namespace Checkpoint123.Heawood
open Finset SimpleGraph StarUnion
open Checkpoint122.Pruning
open PEqualNP.Outside.L_meta_2268_aux.Normal
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- A loss requires an ordinary product outside the survivors or an OR with one pure input. -/
theorem extraOperation {s : State 14} (valid : Valid s) (out : ℕ)
    (spec : ∀ z, (s.wires.getD out default).full z=true ↔ predicate z)
    (mark : none ∈ (s.wires.getD out default).tags) (loss : 0 < missed (s.wires.getD out default)) :
    (s.wires.getD out default).jobs.card+1 ≤ s.products.length+s.bypass := by
  let w := s.wires.getD out default
  have fw := port valid out
  have cap := (budget valid out spec).products
  change w.jobs.card ≤ s.products.length at cap
  by_contra! small
  change s.products.length+s.bypass < w.jobs.card+1 at small
  have zero : s.bypass=0 := by omega
  have imp : w.pure=false := by
    cases hp : w.pure with
    | false => rfl
    | true =>
      have h : w.tags=∅ := fw.empty hp
      change none∈w.tags at mark
      rw [h] at mark
      exact False.elim (notMem_empty _ mark)
  have same : w.jobs=s.products.toFinset := eq_of_subset_of_card_le
    (fun p hp => List.mem_toFinset.mpr (fw.owned p hp)) (s.products.toFinset_card_le.trans (by omega))
  have sound (z) (hz : accepts w z) := (spec z).mp (fw.sound z hz)
  have all : G.edgeFinset ⊆ survivors w := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    have yes := (spec (pair a b)).mpr ((orientation _).mpr
      ⟨a,b,by simpa using he,by simp [pair],by simp [pair]⟩)
    obtain ⟨p,hp,pa,pb⟩ := fw.origin imp zero _ yes
    exact (survives_iff sound a b).mpr (Or.inr ⟨p,same ▸ List.mem_toFinset.mpr hp,pa,pb⟩)
  change 0<(G.edgeFinset \ survivors w).card at loss
  simp [sdiff_eq_empty_iff_subset.mpr all] at loss

/-- The list gives (surviving products, bottom ORs, top ORs, ordinary ANDs plus
mixed ORs, nested ANDs, total gates). Membership expresses necessary counts. -/
def profiles : List (List ℕ) :=
  [[6,11,6,7,1,25], [6,12,6,7,1,26], [6,11,7,7,1,26], [6,11,6,8,1,26],
   [6,11,6,7,2,26], [7,10,7,8,1,26]]

private theorem numericalProfiles (j b t e d l : ℕ)
    (edges : 17≤j+b) (stars : 17≤3*j) (top : j≤t) (extra : j+1≤e)
    (nested : 1≤d) (cost : b+t+e+d=l) (small : l≤26) : [j,b,t,e,d,l]∈profiles := by
  have finish : (j=7 ∨ j=6) := by omega
  rcases finish with rfl|rfl
  · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ : b=10 ∧ t=7 ∧ e=8 ∧ d=1 ∧ l=26 := by omega
    decide
  · by_cases db : d=2
    · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ : b=11 ∧ t=6 ∧ e=7 ∧ d=2 ∧ l=26 := by omega
      decide
    by_cases bb : b=12
    · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ : b=12 ∧ t=6 ∧ e=7 ∧ d=1 ∧ l=26 := by omega
      decide
    by_cases tt : t=7
    · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ : b=11 ∧ t=7 ∧ e=7 ∧ d=1 ∧ l=26 := by omega
      decide
    by_cases ee : e=8
    · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ : b=11 ∧ t=6 ∧ e=8 ∧ d=1 ∧ l=26 := by omega
      decide
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ : b=11 ∧ t=6 ∧ e=7 ∧ d=1 ∧ l=25 := by omega
    decide

theorem fourProfiles (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) (loss : missed ((run 14 gs).wires.getD out default)=4) :
    let s := run 14 gs
    let w := s.wires.getD out default
    [w.jobs.card,s.bottom.length,s.top.length,s.products.length+s.bypass,s.dropped,gs.length] ∈ profiles := by
  let s := run 14 gs
  let w := s.wires.getD out default
  obtain ⟨valid,count⟩ := run_valid 14 gs
  obtain ⟨sub,low,cubic,_,top,_⟩ := budget valid out spec
  obtain ⟨mark,nested,_,_,_⟩ := nestedNecessary gs out spec short
  have extra := extraOperation valid out spec mark (by omega)
  have tag := card_eraseNone_of_mem mark
  change w.jobs.card=w.tags.card-1 at tag
  change w.tags.card ≤ s.top.length+1 at top
  change w.jobs.card+1 ≤ s.products.length+s.bypass at extra
  change 1 ≤ s.dropped at nested
  change (survivors w).card ≤ w.jobs.card+s.bottom.length at low
  change (survivors w).card≤3*w.jobs.card at cubic
  change s.bottom.length+s.top.length+s.products.length+s.dropped+s.bypass=gs.length at count
  have tally : G.edgeFinset.card=21 := by decide +kernel
  change missed w=4 at loss
  rw [missed,card_sdiff_of_subset sub,tally] at loss
  have edges17 : (survivors w).card=17 := by change 21-(survivors w).card=4 at loss; omega
  change [w.jobs.card,s.bottom.length,s.top.length,s.products.length+s.bypass,s.dropped,gs.length]∈profiles
  apply numericalProfiles
  · omega
  · omega
  · omega
  · exact extra
  · exact nested
  · omega
  · exact short

/-- Every set of surviving ordinary products admits a vertex cover with at most one
center per product. This includes empty products and repeated use of the same center. -/
theorem centers {w : Wire 14} (sound : ∀ z, accepts w z → predicate z) :
    ∃ C : Finset V, C.card ≤ w.jobs.card ∧ survivors w ⊆ incident C := by
  have clean := (describe sound).2
  let side (p : Product 14) := if p.1.card≤1 then p.1 else p.2
  have reg : ∀ v ∉ (∅ : Finset V), (G.neighborSet v).ncard=3 := fun v _ => G.ncard_neighborSet v |>.trans (cubic v)
  have girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length := by
    intro v p cycle
    have := girth_six v p cycle
    omega
  have tiny (p) (hp : p ∈ w.jobs) : (side p).card ≤ 1 := by
    by_cases h : p.1.card≤1
    · simp [side,h]
    · have lim := (cleanProductCount G ∅ reg (by simp) girth p.1 p.2 (clean p hp)).1
      rw [show side p=p.2 by simp [side,h]]
      by_contra! big
      have bad : 2*2 ≤ p.1.card*p.2.card := Nat.mul_le_mul (by omega) (by omega)
      omega
  let C := w.jobs.biUnion side
  refine ⟨C,?_,?_⟩
  · calc
      C.card ≤ ∑ p∈w.jobs, (side p).card := card_biUnion_le
      _ ≤ ∑ _∈w.jobs, 1 := sum_le_sum tiny
      _ = w.jobs.card := by simp
  · intro e he
    obtain ⟨p,hp,a,ha,b,hb,rfl⟩ := (in_survivors w _).mp he
    have adj := clean p hp a ha b hb
    by_cases h : p.1.card≤1
    · have member : a∈C := mem_biUnion.mpr ⟨p,hp,by simpa [side,h] using ha⟩
      exact mem_biUnion.mpr ⟨a,member,mem_image.mpr ⟨b,List.mem_toFinset.mpr adj,rfl⟩⟩
    · have member : b∈C := mem_biUnion.mpr ⟨p,hp,by simpa [side,h] using hb⟩
      exact mem_biUnion.mpr ⟨b,member,mem_image.mpr ⟨a,List.mem_toFinset.mpr adj.symm,Sym2.eq_swap⟩⟩

/-- The six-center census applies whenever four edges are lost through six surviving products. -/
theorem sixCenterCover {w : Wire 14} (sound : ∀ z, accepts w z → predicate z)
    (six : w.jobs.card=6) (loss : missed w=4) :
    ∃ C : Finset V, C.card=6 ∧ survivors w ⊆ incident C ∧
      (survivors w).card=17 ∧ ((incident C).card=17 ∨ (incident C).card=18) := by
  obtain ⟨C,cc,sub⟩ := centers sound
  have valid : survivors w ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨p,hp,a,ha,b,hb,rfl⟩ := (in_survivors w _).mp he
    simpa using (describe sound).2 p hp a ha b hb
  have tally : G.edgeFinset.card=21 := by decide +kernel
  rw [missed,card_sdiff_of_subset valid,tally] at loss
  have stars : ∀ v : V, (star v).card=3 := by decide +kernel
  have cap : (incident C).card ≤ 3*C.card := calc
    (incident C).card ≤ ∑ v∈C, (star v).card := card_biUnion_le
    _ = 3*C.card := by simp [stars,Nat.mul_comm]
  have contained := card_le_card sub
  exact ⟨C,by omega,sub,by omega,by omega⟩

#print axioms fourProfiles
#print axioms centers
#print axioms sixCenterCover
end Checkpoint123.Heawood
