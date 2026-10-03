import Flapjack.Misc.Sptree
import Mathlib.Data.List.Induction
import Lean.Elab.Tactic.Omega

namespace Flapjack

/-- Cursor of the actual even-key insertion fold, for arbitrary initial tree
and cursor. This is Flapjack proof factoring, with no separate HOL original. -/
theorem sptFromList2FoldIndex {α : Type} (values : List α) (start : Nat) (tree : Spt α) :
    (values.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 2, sptInsert acc.1 value acc.2))
      (start, tree)).1 = start + 2 * values.length := by
  induction values generalizing start tree with
  | nil => simp
  | cons value values ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    omega

/-- Exact HOL `domain_fromList2`: every list produces exactly the even keys
`GENLIST (fun index => 2 * index) (LENGTH values)`. Native `Spt`, `List`,
`Nat`, and predicate-valued sets retain the original carriers and quantifiers;
there is no well-formedness, distinctness or payload premise. -/
@[hol "cakeml/misc/miscScript.sml" "domain_fromList2"]
theorem sptDomainFromList2 {α : Type} : ∀ values : List α,
    sptDomain (sptFromList2 values) =
      (fun key => key ∈ (List.range values.length).map (fun index => 2 * index)) := by
  intro values
  induction values using List.reverseRecOn with
  | nil =>
    funext key
    simp [sptDomain, sptFromList2]
  | append_singleton values value ih =>
    have inserted : sptFromList2 (values ++ [value]) =
        sptInsert (2 * values.length) value (sptFromList2 values) := by
      simp only [sptFromList2, List.foldl_append, List.foldl_cons, List.foldl_nil,
        sptFromList2FoldIndex, Nat.zero_add]
    rw [inserted]
    funext key
    apply propext
    change sptMem key (sptInsert (2 * values.length) value (sptFromList2 values)) ↔ _
    rw [sptMem_sptInsert]
    change key = 2 * values.length ∨ sptDomain (sptFromList2 values) key ↔ _
    rw [ih]
    simp [List.range_succ, or_comm]

end Flapjack
