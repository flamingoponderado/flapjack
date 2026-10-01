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

/-- Flapjack proof factoring for the collapsing constructor; no separate HOL
theorem is claimed. The source wf_delete proof unfolds this constructor. -/
private theorem wfMkBN {α : Type} (left right : Spt α)
    (hl : sptWf left = true) (hr : sptWf right = true) :
    sptWf (sptMkBN left right) = true := by
  cases left <;> cases right <;> simp_all [sptMkBN, sptWf, sptIsEmpty]

/-- Flapjack proof factoring for the collapsing value constructor, as above. -/
private theorem wfMkBS {α : Type} (left : Spt α) (value : α) (right : Spt α)
    (hl : sptWf left = true) (hr : sptWf right = true) :
    sptWf (sptMkBS left value right) = true := by
  cases left <;> cases right <;> simp_all [sptMkBS, sptWf, sptIsEmpty]

/-- Literal generic HOL deletion preservation with its sole wf premise. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_delete"]
theorem sptWfDelete {α : Type} : ∀ (tree : Spt α) (key : Nat),
    sptWf tree = true → sptWf (sptDelete key tree) = true := by
  intro tree
  induction tree with
  | ln => intro key hw; rfl
  | ls value =>
      intro key hw
      rw [sptDelete]
      split <;> rfl
  | bn left right ihl ihr =>
      intro key hw
      have hl : sptWf left = true := by simp_all [sptWf]
      have hr : sptWf right = true := by simp_all [sptWf]
      rw [sptDelete]
      split
      · exact hw
      · split
        · exact wfMkBN _ _ (ihl _ hl) hr
        · exact wfMkBN _ _ hl (ihr _ hr)
  | bs left value right ihl ihr =>
      intro key hw
      have hl : sptWf left = true := by simp_all [sptWf]
      have hr : sptWf right = true := by simp_all [sptWf]
      rw [sptDelete]
      split
      · simpa [sptWf] using hw
      · split
        · exact wfMkBS _ _ _ (ihl _ hl) hr
        · exact wfMkBS _ _ _ hl (ihr _ hr)

end Flapjack
