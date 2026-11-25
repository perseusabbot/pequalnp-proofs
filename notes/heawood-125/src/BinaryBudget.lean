import PrunedProgram

namespace Checkpoint125.Binary
open Finset

inductive Tree (A : Type) where
  | leaf (x : A)
  | gate (isOr : Bool) (left right : Tree A)
  deriving DecidableEq

namespace Tree
variable {A : Type} [DecidableEq A]

def inputs : Tree A → List A
  | .leaf a => [a]
  | .gate _ a b => a.inputs++b.inputs
def vars (e : Tree A) := e.inputs.toFinset

@[simp] theorem leafVars (v : A) : (leaf v).vars={v} := by simp [vars,inputs]
@[simp] theorem gateVars (op : Bool) (a b : Tree A) : (gate op a b).vars=a.vars∪b.vars := by
  simp [vars,inputs]

def eval (ρ : A → Prop) : Tree A → Prop
  | .leaf a => ρ a
  | .gate true a b => a.eval ρ ∨ b.eval ρ
  | .gate false a b => a.eval ρ ∧ b.eval ρ

theorem mono (e : Tree A) {ρ σ : A → Prop} (h : ∀ x∈e.vars, ρ x → σ x) :
    e.eval ρ → e.eval σ := by
  induction e with
  | leaf x => exact h _ (by simp)
  | gate op a b ia ib =>
    have la := ia (fun x hx => h x (by simp [hx]))
    have lb := ib (fun x hx => h x (by simp [hx]))
    cases op
    · exact And.imp la lb
    · exact Or.imp la lb

end Tree
variable {A : Type} [DecidableEq A]

def Ready (gates : List (Tree A)) (e : Tree A) := (∃ x, e=Tree.leaf x) ∨ e∈gates
def Built : List (Tree A) → Prop
  | [] => True
  | e::gs => Built gs ∧ ∃ op a b, e=Tree.gate op a b ∧ Ready gs a ∧ Ready gs b

private theorem frontier (gs : List (Tree A)) (ok : Built gs) (r : Finset (Tree A))
    (ready : ∀ e∈r, Ready gs e) :
    (r.biUnion Tree.vars).card ≤ gs.length+r.card ∧
    ((r.biUnion Tree.vars).card=gs.length+r.card →
      ∑ e∈r, e.inputs.length=(r.biUnion Tree.vars).card) := by
  classical
  induction gs generalizing r with
  | nil =>
    have single (e) (he : e∈r) : ∃ x, e=Tree.leaf x := (ready e he).elim id (by simp)
    have weight : ∑ e∈r, e.inputs.length=r.card := by
      calc
        _ = ∑ _∈r, 1 := sum_congr rfl (fun e he => by obtain ⟨_,rfl⟩ := single e he; rfl)
        _ = _ := by simp
    have size : (r.biUnion Tree.vars).card ≤ r.card := calc
      _ ≤ ∑ e∈r, e.vars.card := card_biUnion_le
      _ = ∑ _∈r, 1 := sum_congr rfl (fun e he => by obtain ⟨_,rfl⟩ := single e he; simp)
      _ = _ := by simp
    simp only [List.length_nil,Nat.zero_add]
    exact ⟨size,fun h => weight.trans h.symm⟩
  | cons e gs ih =>
    obtain ⟨prev,op,a,b,rfl,ra,rb⟩ := ok
    let root := Tree.gate op a b
    by_cases used : root∈r
    · let rest := r.erase root
      let next := insert a (insert b rest)
      have prep (z) (hz : z∈rest) : Ready gs z := by
        rcases ready z (mem_of_mem_erase hz) with lit|old
        · exact Or.inl lit
        · exact Or.inr ((List.mem_cons.mp old).resolve_left (ne_of_mem_erase hz))
      have rn : ∀ z∈next, Ready gs z := by
        intro z hz
        rcases mem_insert.mp hz with rfl|hz
        · exact ra
        rcases mem_insert.mp hz with rfl|hz
        · exact rb
        exact prep _ hz
      have restore : insert root rest=r := insert_erase used
      have uv : next.biUnion Tree.vars=r.biUnion Tree.vars := by
        rw [←restore]
        simp [next,root,union_assoc]
      obtain ⟨cap,balance⟩ := ih prev next rn
      rw [uv] at cap balance
      have tailSize : rest.card+1=r.card := card_erase_add_one used
      have addB := card_insert_le b rest
      have addA := card_insert_le a (insert b rest)
      change next.card ≤ _ at addA
      simp only [List.length_cons]
      refine ⟨by omega,?_⟩
      intro tight
      have bn : b∉rest := by
        intro bad
        rw [insert_eq_of_mem bad] at addA
        omega
      have an : a∉insert b rest := by
        intro bad
        have eq : next=insert b rest := insert_eq_of_mem bad
        rw [eq] at cap
        omega
      have sums := balance (by omega)
      have sumEq : ∑ z∈r, z.inputs.length=∑ z∈next, z.inputs.length := by
        rw [←restore,sum_insert (notMem_erase root r)]
        simp only [next,sum_insert an,sum_insert bn,root,Tree.inputs,List.length_append]
        exact Nat.add_assoc ..
      exact sumEq.trans sums
    · have rn (z) (hz : z∈r) : Ready gs z := by
        rcases ready z hz with lit|old
        · exact Or.inl lit
        · rcases List.mem_cons.mp old with rfl|mem
          · exact False.elim (used hz)
          · exact Or.inr mem
      have bound := (ih prev r rn).1
      simp only [List.length_cons]
      exact ⟨by omega,by omega⟩

/-- A shared binary computation with g listed gates uses at most g+1 different
leaves. Equality forces every leaf to occur only once in the unfolded output. -/
theorem inputBudget {gs : List (Tree A)} (built : Built gs) {e : Tree A} (ready : Ready gs e) :
    e.vars.card ≤ gs.length+1 ∧ (e.vars.card=gs.length+1 → e.inputs.Nodup) := by
  have f := frontier gs built {e} (fun t ht => (mem_singleton.mp ht) ▸ ready)
  simp only [singleton_biUnion,card_singleton,sum_singleton] at f
  refine ⟨f.1,fun eq => ?_⟩
  exact List.dedup_eq_self.mp (List.Sublist.eq_of_length (List.dedup_sublist e.inputs)
    (by simpa only [Tree.vars,List.card_toFinset] using (f.2 eq).symm))

#print axioms inputBudget
end Checkpoint125.Binary
