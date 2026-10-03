import Flapjack.Misc.Sorting

/-!
# CakeML misc `PERM_PART` and `PERM_PARTITION`

Exact ports of `cakeml/misc/miscScript.sml` `PERM_PART` (1419-1438) and
`PERM_PARTITION` (1440-1444) over the tagged HOL sorting `holPart`,
`holPartition` and `holPerm`.
-/

namespace Flapjack

/-- Exact HOL `PERM_PART` (`miscScript.sml:1419-1438`). -/
@[hol "cakeml/misc/miscScript.sml" "PERM_PART"]
theorem permPart {α : Type} :
    ∀ (P : α → Bool) (L l1 l2 p q : List α),
      (p, q) = holPart P L l1 l2 → holPerm (L ++ (l1 ++ l2)) (p ++ q) := by
  intro P L
  induction L with
  | nil =>
      intro l1 l2 p q h
      simp only [holPart, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [holPerm_iff]
      exact List.Perm.refl _
  | cons h t ih =>
      intro l1 l2 p q he
      simp only [holPart] at he
      rw [holPerm_iff]
      split at he
      · have := (holPerm_iff _ _).mp (ih (h :: l1) l2 p q he)
        refine List.Perm.trans ?_ this
        simp only [List.cons_append]
        exact List.perm_middle.symm
      · have := (holPerm_iff _ _).mp (ih l1 (h :: l2) p q he)
        refine List.Perm.trans ?_ this
        simp only [List.cons_append]
        refine List.Perm.trans ?_ (List.Perm.append_left t (List.perm_middle (l₁ := l1)).symm)
        exact List.perm_middle.symm

/-- Exact HOL `PERM_PARTITION` (`miscScript.sml:1440-1444`). -/
@[hol "cakeml/misc/miscScript.sml" "PERM_PARTITION"]
theorem permPartitionMisc {α : Type} :
    ∀ (P : α → Bool) (L A B : List α), (A, B) = holPartition P L → holPerm L (A ++ B) := by
  intro P L A B h
  have := permPart P L [] [] A B h
  simpa using this

end Flapjack
