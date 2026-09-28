import Flapjack.Pancake.LoopLang.AssignedVars

/-!
Exact `loopPropsScript.sml` assigned-variable theorem ports over the faithful
`HolLoopProg` carrier. Production LoopProg remains a separate untagged analogue.
-/

namespace Flapjack

/-- Exact HOL `assigned_vars_seq_split` with HOL binder order `q`, then `p`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "assigned_vars_seq_split"
  (words_as_type_indexed_bitvec)]
theorem holAssignedVarsSeqSplit {width : Nat} [NeZero width]
    (q p : HolLoopProg width) :
    holLoopAssignedVars (.seq p q) = holLoopAssignedVars p ++ holLoopAssignedVars q := by
  rfl

/-- Exact HOL `assigned_vars_nested_seq_split` over `HolLoopProg`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml"
  "assigned_vars_nested_seq_split" (words_as_type_indexed_bitvec)]
theorem holAssignedVarsNestedSeqSplit {width : Nat} [NeZero width]
    (p q : List (HolLoopProg width)) :
    holLoopAssignedVars (loopNestedSeqHOL (p ++ q)) =
      holLoopAssignedVars (loopNestedSeqHOL p) ++
        holLoopAssignedVars (loopNestedSeqHOL q) := by
  induction p with
  | nil => simp [loopNestedSeqHOL, holLoopAssignedVars]
  | cons statement statements ih =>
      simp [loopNestedSeqHOL, holLoopAssignedVars, ih, List.append_assoc]

/-- Exact HOL `assigned_vars_nested_assign`. `List.zipWith` renders HOL
    `MAP2`; the sole equal-length premise is preserved. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml"
  "assigned_vars_nested_assign" (words_as_type_indexed_bitvec)]
theorem holAssignedVarsNestedAssign {width : Nat} [NeZero width]
    (xs : List Nat) (ys : List (HolLoopExp width))
    (hLength : xs.length = ys.length) :
    holLoopAssignedVars
      (loopNestedSeqHOL (List.zipWith HolLoopProg.assign xs ys)) = xs := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hLength
  | cons x xs ih =>
      cases ys with
      | nil => simp at hLength
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hLength
          simp [loopNestedSeqHOL, holLoopAssignedVars, ih ys hLength]

end Flapjack
