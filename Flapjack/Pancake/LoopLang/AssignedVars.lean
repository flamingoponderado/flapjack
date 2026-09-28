import Flapjack.Pancake.LoopLang

/-!
Exact `loopLang$assigned_vars` and `nested_seq` definitions. This submodule is
the declaration-level counterpart of `loopLangScript.sml`; the production
list-backed helpers remain in `LoopLive.lean` without HOL tags.
-/

namespace Flapjack

/-- HOL `loopLang$assigned_vars` over its exact width-indexed program carrier. -/
@[hol "cakeml/pancake/loopLangScript.sml" "assigned_vars_def"
  (words_as_type_indexed_bitvec)]
def holLoopAssignedVars {width : Nat} [NeZero width] :
    HolLoopProg width → List Nat
  | .skip => []
  | .assign name _ => [name]
  | .primitive destinations _ _ => destinations
  | .arith operation =>
      match operation with
      | .longMul left right _ _ => [left, right]
      | .longDiv left right _ _ _ => [left, right]
      | .div destination _ _ => [destination]
  | .load32 _ destination => [destination]
  | .loadByte _ destination => [destination]
  | .seq first second => holLoopAssignedVars first ++ holLoopAssignedVars second
  | .ite _ _ _ thenBranch elseBranch _ =>
      holLoopAssignedVars thenBranch ++ holLoopAssignedVars elseBranch
  | .locValue destination _ => [destination]
  | .shMem _ destination _ => [destination]
  | .mark body => holLoopAssignedVars body
  | .loop _ body _ => holLoopAssignedVars body
  | .call none _ _ _ => []
  | .call (some (returns, _)) _ _ none => returns
  | .call (some (returns, _)) _ _ (some (exception, handler, normal, _)) =>
      returns ++ exception :: holLoopAssignedVars handler ++ holLoopAssignedVars normal
  | _ => []

/-- HOL `loopLang$nested_seq` over the exact program carrier. -/
@[hol "cakeml/pancake/loopLangScript.sml" "nested_seq_def"
  (words_as_type_indexed_bitvec)]
def holLoopNestedSeq {width : Nat} [NeZero width] :
    List (HolLoopProg width) → HolLoopProg width
  | [] => .skip
  | statement :: statements => .seq statement (holLoopNestedSeq statements)

end Flapjack
