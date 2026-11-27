import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

namespace Checkpoint138

/-- Five witnesses, each missing just its own entry of a five-element test family. -/
def Crown {α β : Type*} (R : α → β → Prop) (n : ℕ) :=
  ∃ (a : Fin n → α) (b : Fin n → β), ∀ i j, R (a i) (b j) ↔ i ≠ j

/-- Every simultaneous test has a subfamily of at most four tests with the same answers. -/
theorem fourTests {α β : Type*} (R : α → β → Prop) (noFive : ¬ Crown R 5) (S : Finset α) :
    ∃ T ⊆ S, T.card ≤ 4 ∧ ∀ b, (∀ a ∈ T, R a b) ↔ ∀ a ∈ S, R a b := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases small : S.card ≤ 4
    · exact ⟨S, Finset.Subset.rfl, small, fun _ => Iff.rfl⟩
    by_cases erase : ∃ x ∈ S, ∀ b, (∀ a ∈ S.erase x, R a b) → R x b
    · obtain ⟨x, hx, redundant⟩ := erase
      obtain ⟨T,sub,size,same⟩ := ih (S.erase x) (Finset.erase_ssubset hx)
      refine ⟨T,sub.trans (Finset.erase_subset ..),size,fun b => (same b).trans ⟨?_,?_⟩⟩
      · intro e a ha
        by_cases eq : a = x
        · exact eq ▸ redundant b e
        · exact e a (Finset.mem_erase.mpr ⟨eq,ha⟩)
      · intro e a ha
        exact e a (Finset.mem_erase.mp ha).2
    · exfalso
      apply noFive
      have card : Fintype.card (Fin 5) ≤ Fintype.card {x // x ∈ S} := by simpa using (show 5 ≤ S.card by omega)
      let cast : Fin 5 ↪ Fin (Fintype.card {x // x ∈ S}) :=
        ⟨fun i => ⟨i.val,lt_of_lt_of_le i.isLt (by simpa using card)⟩, fun _ _ h => Fin.ext (congrArg (fun z : Fin (Fintype.card {x // x ∈ S}) => z.val) h)⟩
      let f := cast.trans (Fintype.equivFin {x // x ∈ S}).symm.toEmbedding
      have witness (i : Fin 5) : ∃ b, (∀ a ∈ S.erase (f i).val, R a b) ∧ ¬ R (f i).val b := by
        by_contra! h
        apply erase
        exact ⟨(f i).val,(f i).property,h⟩
      choose b hb hn using witness
      refine ⟨fun i => (f i).val,b,fun i j => ⟨?_,?_⟩⟩
      · intro hit eq
        subst i
        exact hn j hit
      · intro ne
        exact hb j _ (Finset.mem_erase.mpr ⟨fun eq => ne (f.injective (Subtype.ext eq)),(f i).property⟩)

theorem transposeCrown {α β : Type*} {R : α → β → Prop} {n : ℕ} :
    Crown (fun b a => R a b) n → Crown R n := by
  rintro ⟨b,a,h⟩
  exact ⟨a,b,fun i j => (h j i).trans ne_comm⟩

#print axioms fourTests
#print axioms transposeCrown

end Checkpoint138
