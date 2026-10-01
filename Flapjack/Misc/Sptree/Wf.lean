import Flapjack.Misc.Sptree

namespace Flapjack

/-- Literal source nonempty result for insertion, without a well-formedness premise. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "insert_notEmpty"]
theorem sptInsertNotEmpty {α : Type} (key : Nat) (value : α) (tree : Spt α) :
    sptIsEmpty (sptInsert key value tree) = false := by
  cases tree <;> rw [sptInsert] <;> by_cases hz : key = 0 <;>
    by_cases hp : key % 2 = 0 <;> simp only [hz, hp, if_true, if_false, sptIsEmpty]

/-- Literal source insertion preserves well-formedness for every payload type. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_insert"]
theorem sptWfInsert {α : Type} : ∀ (key : Nat) (value : α) (tree : Spt α),
    sptWf tree = true → sptWf (sptInsert key value tree) = true := by
  intro key
  induction key using Nat.strongRecOn with
  | ind key ih =>
    intro value tree hw
    by_cases hz : key = 0
    · subst key
      cases tree <;> rw [sptInsert] <;> simp_all [sptWf]
    · have hlt : (key - 1) / 2 < key := by
        have := Nat.div_le_self (key - 1) 2
        omega
      have hrec := ih ((key - 1) / 2) hlt value
      have hnil := hrec .ln rfl
      cases tree <;> rw [sptInsert] <;> by_cases hp : key % 2 = 0 <;>
        simp_all [sptWf, sptInsertNotEmpty]

end Flapjack
