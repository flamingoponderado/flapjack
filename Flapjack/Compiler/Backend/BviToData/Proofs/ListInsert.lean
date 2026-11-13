module

public import Flapjack.Compiler.Backend.BviToData.Assign

@[expose] public section

/-! Sparse live-name set facts for the BVI-to-data compiler. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- Inserting names already present in a generated set leaves it unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "list_insert_list_to_num_set"]
theorem listInsert_namesOfList (xs ys zs : List Nat) :
    sptListInsert xs (namesOfList (xs ++ ys ++ zs)) = namesOfList (xs ++ ys ++ zs) := by
  have present (key : Nat) (names : List Nat) (mem : key ∈ names) :
      sptInsert key () (namesOfList names) = namesOfList names := by
    induction names with
    | nil => simp at mem
    | cons name names ih =>
      simp only [List.mem_cons] at mem
      rcases mem with same | rest
      · subst name
        simp [namesOfList, sptInsert_insert_shadow]
      · by_cases same : key = name
        · subst name
          simp [namesOfList, sptInsert_insert_shadow]
        · simp only [namesOfList]
          rw [sptInsert_swap key name () () _ same, ih rest]
  have stable (todo : List Nat) (tree : NumSet)
      (fixed : ∀ key ∈ todo, sptInsert key () tree = tree) :
      sptListInsert todo tree = tree := by
    induction todo generalizing tree with
    | nil => rfl
    | cons key rest ih =>
      simp only [sptListInsert, fixed key (by simp)]
      exact ih tree (fun k hk => fixed k (by simp [hk]))
  apply stable
  intro key mem
  apply present
  simp [mem]

end Flapjack.Compiler.Backend.BviToData
