import SixLost
import FourProfiles

namespace Checkpoint124.Heawood
open Finset SimpleGraph Checkpoint122.Pruning
open PEqualNP.Outside.L_meta_3004_aux.Controls

/-- Exactly the edge indices whose endpoints both avoid the chosen centers. -/
def outside (cs : List V) := (List.finRange 21).filter (fun i =>
  !cs.contains (endpoint i false) && !cs.contains (endpoint i true))
def fiveOptions := ((List.finRange 14).sublistsLen 5).filter (fun cs => (outside cs).length==6)

private theorem injectiveEdge : Function.Injective edge := by
  change ∀ i j : Fin 21, edge i=edge j → i=j
  decide +kernel

private theorem coversPair (C : Finset V) {a b} (adj : G.Adj a b) :
    s(a,b)∈incident C ↔ a∈C ∨ b∈C := by
  constructor
  · intro h
    obtain ⟨v,hv,mem⟩ := mem_biUnion.mp h
    obtain ⟨u,_,eq⟩ := mem_image.mp mem
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (ha|hb)
    · exact mem_biUnion.mpr ⟨a,ha,mem_image.mpr ⟨b,List.mem_toFinset.mpr adj,rfl⟩⟩
    · exact mem_biUnion.mpr ⟨b,hb,mem_image.mpr ⟨a,List.mem_toFinset.mpr adj.symm,Sym2.eq_swap⟩⟩

theorem outsideEdges (cs : List V) :
    (outside cs).toFinset.image edge=G.edgeFinset \ incident cs.toFinset := by
  have listed (i : Fin 21) : i∈outside cs ↔ endpoint i false∉cs ∧ endpoint i true∉cs := by
    simp [outside]
  ext e
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    obtain ⟨a,b⟩ := (listed i).mp (List.mem_toFinset.mp hi)
    refine mem_sdiff.mpr ⟨indexedEdges ▸ mem_image.mpr ⟨i,mem_univ _,rfl⟩,?_⟩
    intro he
    exact ((coversPair _ (indexedAdj i)).mp he).elim (fun h => a (List.mem_toFinset.mp h))
      (fun h => b (List.mem_toFinset.mp h))
  · intro h
    obtain ⟨he,no⟩ := mem_sdiff.mp h
    rw [←indexedEdges] at he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    apply mem_image.mpr
    refine ⟨i,List.mem_toFinset.mpr ((listed i).mpr ⟨?_,?_⟩),rfl⟩
    · exact fun h => no ((coversPair _ (indexedAdj i)).mpr (Or.inl (List.mem_toFinset.mpr h)))
    · exact fun h => no ((coversPair _ (indexedAdj i)).mpr (Or.inr (List.mem_toFinset.mpr h)))

theorem fiveCenterCase {w : Wire 14} (sound : ∀ z, accepts w z → predicate z)
    (jobs : w.jobs.card=5) (loss : missed w=6) :
    ∃ cs∈fiveOptions, survivors w=incident cs.toFinset ∧
      G.edgeFinset \ survivors w=(outside cs).toFinset.image edge := by
  have sub : survivors w ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨p,hp,a,ha,b,hb,rfl⟩ := (in_survivors w _).mp he
    simpa using (describe sound).2 p hp a ha b hb
  have tally : G.edgeFinset.card=21 := by decide +kernel
  have remaining : (survivors w).card=15 := by
    rw [missed,card_sdiff_of_subset sub,tally] at loss
    omega
  obtain ⟨C,size,fit⟩ := Checkpoint123.Heawood.centers sound
  have degree : ∀ v, (star v).card=3 := by decide +kernel
  have cap : (incident C).card ≤ 3*C.card := calc
    _ ≤ ∑ v∈C, (star v).card := card_biUnion_le
    _ = _ := by simp [degree,Nat.mul_comm]
  have reverseSize := card_le_card fit
  have sz : C.card=5 := by omega
  have exactCover : survivors w=incident C := eq_of_subset_of_card_le fit (by omega)
  let cs := (List.finRange 14).filter (fun v => decide (v∈C))
  have eq : cs.toFinset=C := by ext x; simp [cs]
  have nodup := (List.nodup_finRange 14).filter (fun v => decide (v∈C))
  have length : cs.length=5 := by rw [←List.toFinset_card_of_nodup nodup,eq,sz]
  have cover : survivors w=incident cs.toFinset := by rwa [eq]
  have missing := (outsideEdges cs).symm
  rw [←cover] at missing
  have sizeLost := congrArg Finset.card missing
  have distinct : (outside cs).Nodup := (List.nodup_finRange 21).filter _
  rw [card_image_of_injective _ injectiveEdge,List.toFinset_card_of_nodup distinct] at sizeLost
  change missed w=(outside cs).length at sizeLost
  exact ⟨cs,List.mem_filter.mpr ⟨List.mem_sublistsLen.mpr ⟨List.filter_sublist,length⟩,
    by simp [←sizeLost,loss]⟩,cover,missing⟩

private def degreeIn (L : List (Fin 21)) (v : V) :=
  L.countP (fun i => endpoint i false==v || endpoint i true==v)
private def degreeCount (L : List (Fin 21)) (d : ℕ) :=
  (List.finRange 14).countP (fun v => degreeIn L v==d)

/-- Two degree-three centers, a shared degree-two leaf, and four private leaves.
Each edge touches exactly one of the centers. -/
def twoStars (L : List (Fin 21)) :=
  degreeCount L 3==2 && degreeCount L 2==1 && degreeCount L 1==4 &&
    L.all (fun i => (degreeIn L (endpoint i false)==3) != (degreeIn L (endpoint i true)==3))

/-- Each edge joins a degree-two center to a leaf. There are three such centers. -/
def threePaths (L : List (Fin 21)) :=
  degreeCount L 2==3 && degreeCount L 1==6 &&
    L.all (fun i => let a := degreeIn L (endpoint i false)
                    let b := degreeIn L (endpoint i true)
                    (a==1 && b==2) || (a==2 && b==1))

theorem fiveCounts : fiveOptions.length=56 ∧
    (fiveOptions.map (fun cs => (outside cs).toFinset)).Nodup ∧
    fiveOptions.countP (fun cs => twoStars (outside cs))=42 ∧
    fiveOptions.countP (fun cs => threePaths (outside cs))=14 ∧
    fiveOptions.all (fun cs => twoStars (outside cs) != threePaths (outside cs))=true := by
  set_option maxRecDepth 25000 in
  set_option maxHeartbeats 0 in
  decide +kernel

theorem sixAtTwentyFive (gs : List Op) (out : ℕ)
    (spec : ∀ z, ((run 14 gs).wires.getD out default).full z=true ↔ predicate z)
    (size : gs.length=25) (lost : missed ((run 14 gs).wires.getD out default)=6) :
    let w := (run 14 gs).wires.getD out default
    ∃ cs∈fiveOptions, G.edgeFinset \ survivors w=(outside cs).toFinset.image edge ∧
      (twoStars (outside cs)=true ∨ threePaths (outside cs)=true) := by
  have five := ((sixProfile gs out spec (by omega) lost).2.2.2 size).1
  have sound := (port (run_valid 14 gs).1 out).sound
  obtain ⟨cs,hcs,_,eq⟩ := fiveCenterCase (fun z h => (spec z).mp (sound z h)) five lost
  have classes := List.all_eq_true.mp fiveCounts.2.2.2.2 cs hcs
  refine ⟨cs,hcs,eq,?_⟩
  cases a : twoStars (outside cs) <;> cases b : threePaths (outside cs) <;> simp_all

#print axioms outsideEdges
#print axioms fiveCenterCase
#print axioms fiveCounts
#print axioms sixAtTwentyFive
end Checkpoint124.Heawood
