import Flapjack.Misc.Sptree

namespace Flapjack

/-- Literal insertion as a left-biased union with a singleton, on arbitrary
trees. The source statement does not require well-formedness. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "insert_union"]
theorem sptInsert_union {α : Type} (key : Nat) (value : α) (tree : Spt α) :
    sptInsert key value tree = sptUnion (sptInsert key value .ln) tree := by
  induction key using Nat.strongRecOn generalizing tree with
  | ind key ih =>
      by_cases zero : key = 0
      · subst key
        cases tree <;> simp [sptInsert, sptUnion]
      · have smaller : (key - 1) / 2 < key := by omega
        have recur := ih ((key - 1) / 2) smaller
        by_cases even : key % 2 = 0
        <;> cases tree
        <;> (conv => lhs; rw [sptInsert]; simp only [zero, even, if_true, if_false])
        <;> (conv => rhs; rw [sptInsert.eq_1]; simp only [zero, even, if_true, if_false])
        <;> simp only [sptUnion, ← recur]

/-- Literal associativity of the tree operation, including malformed trees
and overlapping keys with arbitrary stored values. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "union_assoc"]
theorem sptUnion_assoc {α : Type} (first second third : Spt α) :
    sptUnion first (sptUnion second third) = sptUnion (sptUnion first second) third := by
  induction first generalizing second third
  <;> cases second <;> cases third <;> simp_all [sptUnion]

/-- Literal union commutativity for the source's unit-valued number sets.
It is not asserted for arbitrary value types. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "union_num_set_sym"]
theorem sptUnion_numSet_sym (first second : Spt Unit) :
    sptUnion first second = sptUnion second first := by
  induction first generalizing second
  <;> cases second <;> simp_all [sptUnion]

/-- The source's reverse singleton-union equation, with no tree invariant. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "union_insert_LN"]
theorem sptUnion_insert_ln {α : Type} (key : Nat) (value : α) (tree : Spt α) :
    sptUnion (sptInsert key value .ln) tree = sptInsert key value tree :=
  (sptInsert_union key value tree).symm

end Flapjack
