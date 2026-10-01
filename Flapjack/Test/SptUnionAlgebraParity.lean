import Flapjack.Misc.Sptree.UnionAlgebra

/-! Same-input original tree-algebra observations, including malformed trees. -/
namespace Flapjack.Test.SptUnionAlgebraParity
open Flapjack

example {α : Type} (key : Nat) (value : α) (tree : Spt α) :
    sptInsert key value tree = sptUnion (sptInsert key value .ln) tree :=
  sptInsert_union key value tree

example {α : Type} (a b c : Spt α) :
    sptUnion a (sptUnion b c) = sptUnion (sptUnion a b) c :=
  sptUnion_assoc a b c

example (a b : Spt Unit) : sptUnion a b = sptUnion b a :=
  sptUnion_numSet_sym a b

example {α : Type} (key : Nat) (value : α) (tree : Spt α) :
    sptUnion (sptInsert key value .ln) tree = sptInsert key value tree :=
  sptUnion_insert_ln key value tree

-- spt_union_insert_empty_0
example : sptInsert 0 42 .ln = sptUnion (sptInsert 0 42 .ln) .ln :=
  sptInsert_union _ _ _

-- spt_union_insert_empty_1
example : sptInsert 1 42 .ln = sptUnion (sptInsert 1 42 .ln) .ln :=
  sptInsert_union _ _ _

-- spt_union_insert_empty_2
example : sptInsert 2 42 .ln = sptUnion (sptInsert 2 42 .ln) .ln :=
  sptInsert_union _ _ _

-- spt_union_insert_empty_17
example : sptInsert 17 42 .ln = sptUnion (sptInsert 17 42 .ln) .ln :=
  sptInsert_union _ _ _

-- spt_union_insert_leaf_0
example : sptInsert 0 42 (.ls 5) = sptUnion (sptInsert 0 42 .ln) (.ls 5) :=
  sptInsert_union _ _ _

-- spt_union_insert_leaf_1
example : sptInsert 1 42 (.ls 5) = sptUnion (sptInsert 1 42 .ln) (.ls 5) :=
  sptInsert_union _ _ _

-- spt_union_insert_leaf_2
example : sptInsert 2 42 (.ls 5) = sptUnion (sptInsert 2 42 .ln) (.ls 5) :=
  sptInsert_union _ _ _

-- spt_union_insert_leaf_17
example : sptInsert 17 42 (.ls 5) = sptUnion (sptInsert 17 42 .ln) (.ls 5) :=
  sptInsert_union _ _ _

-- spt_union_insert_empty_internal_0
example : sptInsert 0 42 (.bn .ln .ln) = sptUnion (sptInsert 0 42 .ln) (.bn .ln .ln) :=
  sptInsert_union _ _ _

-- spt_union_insert_empty_internal_1
example : sptInsert 1 42 (.bn .ln .ln) = sptUnion (sptInsert 1 42 .ln) (.bn .ln .ln) :=
  sptInsert_union _ _ _

-- spt_union_insert_empty_internal_2
example : sptInsert 2 42 (.bn .ln .ln) = sptUnion (sptInsert 2 42 .ln) (.bn .ln .ln) :=
  sptInsert_union _ _ _

-- spt_union_insert_empty_internal_17
example : sptInsert 17 42 (.bn .ln .ln) = sptUnion (sptInsert 17 42 .ln) (.bn .ln .ln) :=
  sptInsert_union _ _ _

-- spt_union_insert_branch_0
example : sptInsert 0 42 (.bn (.ls 7) (.ls 8)) = sptUnion (sptInsert 0 42 .ln) (.bn (.ls 7) (.ls 8)) :=
  sptInsert_union _ _ _

-- spt_union_insert_branch_1
example : sptInsert 1 42 (.bn (.ls 7) (.ls 8)) = sptUnion (sptInsert 1 42 .ln) (.bn (.ls 7) (.ls 8)) :=
  sptInsert_union _ _ _

-- spt_union_insert_branch_2
example : sptInsert 2 42 (.bn (.ls 7) (.ls 8)) = sptUnion (sptInsert 2 42 .ln) (.bn (.ls 7) (.ls 8)) :=
  sptInsert_union _ _ _

-- spt_union_insert_branch_17
example : sptInsert 17 42 (.bn (.ls 7) (.ls 8)) = sptUnion (sptInsert 17 42 .ln) (.bn (.ls 7) (.ls 8)) :=
  sptInsert_union _ _ _

-- spt_union_insert_root_0
example : sptInsert 0 42 (.bs (.ls 7) 5 (.ls 8)) = sptUnion (sptInsert 0 42 .ln) (.bs (.ls 7) 5 (.ls 8)) :=
  sptInsert_union _ _ _

-- spt_union_insert_root_1
example : sptInsert 1 42 (.bs (.ls 7) 5 (.ls 8)) = sptUnion (sptInsert 1 42 .ln) (.bs (.ls 7) 5 (.ls 8)) :=
  sptInsert_union _ _ _

-- spt_union_insert_root_2
example : sptInsert 2 42 (.bs (.ls 7) 5 (.ls 8)) = sptUnion (sptInsert 2 42 .ln) (.bs (.ls 7) 5 (.ls 8)) :=
  sptInsert_union _ _ _

-- spt_union_insert_root_17
example : sptInsert 17 42 (.bs (.ls 7) 5 (.ls 8)) = sptUnion (sptInsert 17 42 .ln) (.bs (.ls 7) 5 (.ls 8)) :=
  sptInsert_union _ _ _

-- spt_union_insert_malformed_nested_0
example : sptInsert 0 42 (.bs (.bn .ln .ln) 5 (.bn (.ls 8) .ln)) = sptUnion (sptInsert 0 42 .ln) (.bs (.bn .ln .ln) 5 (.bn (.ls 8) .ln)) :=
  sptInsert_union _ _ _

-- spt_union_insert_malformed_nested_1
example : sptInsert 1 42 (.bs (.bn .ln .ln) 5 (.bn (.ls 8) .ln)) = sptUnion (sptInsert 1 42 .ln) (.bs (.bn .ln .ln) 5 (.bn (.ls 8) .ln)) :=
  sptInsert_union _ _ _

-- spt_union_insert_malformed_nested_2
example : sptInsert 2 42 (.bs (.bn .ln .ln) 5 (.bn (.ls 8) .ln)) = sptUnion (sptInsert 2 42 .ln) (.bs (.bn .ln .ln) 5 (.bn (.ls 8) .ln)) :=
  sptInsert_union _ _ _

-- spt_union_insert_malformed_nested_17
example : sptInsert 17 42 (.bs (.bn .ln .ln) 5 (.bn (.ls 8) .ln)) = sptUnion (sptInsert 17 42 .ln) (.bs (.bn .ln .ln) 5 (.bn (.ls 8) .ln)) :=
  sptInsert_union _ _ _

-- spt_union_left_bias
example : sptUnion (.ls 11) (.ls 22) = (.ls 11 : Spt Nat) := by
  decide +kernel

-- spt_union_nat_noncomm
example : sptUnion (.ls 11) (.ls 22) ≠ (sptUnion (.ls 22) (.ls 11) : Spt Nat) := by
  decide +kernel

-- spt_union_malformed_retained
example : sptUnion (.bn .ln .ln) .ln = (.bn .ln .ln : Spt Nat) := by
  decide +kernel

-- spt_union_unit_malformed
example : sptUnion (.bn .ln .ln) (.ls ()) = (sptUnion (.ls ()) (.bn .ln .ln) : Spt Unit) := by
  decide +kernel

end Flapjack.Test.SptUnionAlgebraParity
