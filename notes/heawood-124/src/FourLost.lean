import StarRestriction
import RestrictionSupport

namespace Checkpoint123.Heawood
open Finset StarUnion
open Checkpoint122.Pruning Checkpoint123.Restriction
open Checkpoint121.Heawood (neighborhood)
open PEqualNP.Outside.L_meta_3004_aux.Controls

private def select (S : Support 14) (x : V) := decide (x∈S)
private theorem selectTrue (S : Support 14) (x : V) : select S x=true ↔ x∈S := by simp [select]

private theorem pairEssential (v : V) {i : V} (hi : i∈terminals v) :
    ∃ u ∈ neighborhood v, i∈({v,u} : Support 14) := by
  rcases mem_insert.mp hi with eq|hn
  · subst i
    obtain ⟨u,hu⟩ : (neighborhood v).Nonempty := card_pos.mp (by rw [threeNeighbors]; decide)
    exact ⟨u,hu,by simp⟩
  · exact ⟨i,hn,by simp⟩

/-- On the star alone, changing any one of the four input coordinates can change the answer. -/
theorem starNeedsFour {w : Wire 14} (spec : ∀ z, w.full z=true ↔ predicate z)
    (v : V) {A : Support 14} (track : Tracks (terminals v) A w.full) : 4 ≤ A.card := by
  have sub : terminals v ⊆ A := by
    intro i hi
    by_contra missing
    obtain ⟨u,hu,edgeHas⟩ := pairEssential v hi
    let E : Support 14 := {v,u}
    change i∈E at edgeHas
    have inside : E ⊆ terminals v := by
      intro a ha
      rcases mem_insert.mp ha with rfl|he
      · exact mem_insert_self .. 
      · obtain rfl := mem_singleton.mp he
        exact mem_insert_of_mem hu
    have loc {S} (subS : S ⊆ terminals v) : Local (terminals v) (select S) :=
      fun a yes => subS ((selectTrue _ _).mp yes)
    have same := track (select E) (select (E.erase i)) (loc inside) (loc (fun _ hj => inside (mem_of_mem_erase hj)))
      (fun j hj => by
        have ne : j≠i := fun eq => missing (eq ▸ hj)
        simp [select,ne])
    have pos : predicate (select E) := (orientation _).mpr
      ⟨v,u,List.mem_toFinset.mp hu,(selectTrue _ _).mpr (by simp [E]),(selectTrue _ _).mpr (by simp [E])⟩
    have neg := (spec _).mp (same ▸ (spec _).mpr pos)
    obtain ⟨a,b,adj,ha,hb⟩ := (orientation _).mp neg
    have small : (E.erase i).card≤1 := by
      rw [card_erase_of_mem edgeHas]
      have h : E.card ≤ 2 := card_le_two
      omega
    exact adj.ne ((card_le_one.mp small) _ ((selectTrue _ _).mp ha) _ ((selectTrue _ _).mp hb))
  simpa [fourTerminals] using card_le_card sub

private theorem otherProducts (J : Finset (Product 14)) (P : List (Product 14))
    (owned : ∀ p ∈ J, p∈P) :
    J.card + (P.filter (fun p => decide (p ∉ J))).length ≤ P.length := by
  let live := P.filter (fun p => decide (p∈J))
  have sub : J ⊆ live.toFinset := fun p hp => List.mem_toFinset.mpr
    (List.mem_filter.mpr ⟨owned p hp,by simpa using hp⟩)
  have count := (card_le_card sub).trans live.toFinset_card_le
  have total := List.length_eq_countP_add_countP (l:=P) (fun p => decide (p∈J))
  simp only [List.countP_eq_length_filter] at total
  have split : P.length = live.length + (P.filter (fun p => decide (p ∉ J))).length := by
    simpa [live] using total
  omega

/-- Restoring all four essential coordinates puts a lower bound on the exceptional gates. -/
theorem starCost (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z) {v : V}
    (lost : G.edgeFinset \ survivors ((run 14 gs).wires.getD out default) = star v)
    (six : ((run 14 gs).wires.getD out default).jobs.card=6)
    (twelve : (run 14 gs).bottom.length=12) :
    let s := run 14 gs
    4 ≤ 2*(s.products.length-6)+s.bypass+s.dropped := by
  let s := run 14 gs
  let w := s.wires.getD out default
  have valid : Valid s := (run_valid 14 gs).1
  have fw := port valid out
  have sound (z) (h : accepts w z) := (spec z).mp (fw.sound z h)
  have thin := bottomThin s.bottom valid.bottom (fun p hp => valid.operands p (fw.owned p hp)) sound lost six twelve
  have dead (p) (hp : p∈w.jobs) (x) (lx : Local (terminals v) x) := deadOnStar sound lost p hp lx
  obtain ⟨A,size,tracks⟩ := supportBudget (terminals v) w.jobs gs thin dead
  have imp : w.pure=false := by
    cases pure : w.pure with
    | false => rfl
    | true =>
      have none : w.tags=∅ := fw.empty pure
      have empty : w.jobs=∅ := by simp [Wire.jobs,none]
      change w.jobs.card=6 at six
      simp [empty] at six
  have needs : 4≤A.card := starNeedsFour spec v (tracks out imp)
  have count := otherProducts w.jobs s.products fw.owned
  change w.jobs.card=6 at six
  change A.card ≤ 2*(s.products.filter (fun p => decide (p ∉ w.jobs))).length+s.bypass+s.dropped at size
  change 4 ≤ 2*(s.products.length-6)+s.bypass+s.dropped
  omega

/-- All interleavings and fanouts are allowed. Cutting nested ANDs in a Heawood
circuit with at most 26 gates loses at least four minimal positive assignments. -/
theorem fourLost (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (short : gs.length≤26) : 4 ≤ missed ((run 14 gs).wires.getD out default) := by
  let s := run 14 gs
  let w := s.wires.getD out default
  obtain ⟨_,_,atLeast,_,eqCase⟩ := nestedNecessary gs out spec short
  by_contra! small
  have three : missed w=3 := by change 3 ≤ missed w at atLeast; change missed w<4 at small; omega
  obtain ⟨_,one,six,twelve,_,seven⟩ := eqCase three
  have valid : Valid s := (run_valid 14 gs).1
  have sub := (budget valid out spec).sub
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have loss := three
  rw [missed,card_sdiff_of_subset sub,tally] at loss
  obtain ⟨v,lost⟩ := missingStar (fun z h => (spec z).mp ((port valid out).sound z h)) six (by omega)
  have needs := starCost gs out spec lost six twelve
  change 4 ≤ 2*(s.products.length-6)+s.bypass+s.dropped at needs
  change s.dropped=1 at one
  change s.products.length+s.bypass=7 at seven
  have pr := (budget valid out spec).products
  change w.jobs.card ≤ s.products.length at pr
  change w.jobs.card=6 at six
  omega

/-- Specialization to the exact 65 opening wire pairs and both gate flags at the desk. -/
theorem postedFourLost (i : Fin 65) (f g : Bool) (tail : List (Fin 8192))
    (h : Checkpoint122.Posted.Witness i f g tail) :
    let qs := Checkpoint122.Posted.codes i f g tail
    4 ≤ missed ((run 14 (qs.map Checkpoint122.Posted.decode)).wires.getD (13+qs.length) default) := by
  apply fourLost _ _ (Checkpoint122.Posted.semantics _ h.2)
  have len := h.1
  simp only [List.length_map,Checkpoint122.Posted.codes,List.length_cons]
  omega

#print axioms starNeedsFour
#print axioms starCost
#print axioms fourLost
#print axioms postedFourLost
end Checkpoint123.Heawood
