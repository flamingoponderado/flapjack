module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap
public import Flapjack.Misc.Sptree.Subspt
public import Flapjack.Misc.SptreeLookup
public import Flapjack.HolRef

@[expose] public section

/-!
# An upper bound on the heap size reachable from a value list

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:21`
`approx_of_def`: the same traversal as `size_of` but without the visited set,
so it over-approximates the reachable heap space. The termination measure is
HOL's `(sptree$size refs, list_size v_size vs)`, rendered with `sptSize` and
Lean's `sizeOf`.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem
open Classical

/-- Upper bound on the heap space reachable from a value list, ignoring the
    visited set. Port of HOL `approx_of`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "approx_of_def"]
noncomputable def approxOf (limits : Limits) (values : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) : Nat :=
  match values with
  | [] => 0
  | x :: y :: ys =>
      approxOf limits [x] refs + approxOf limits (y :: ys) refs
  | [.word64 _] => 3
  | [.number n] =>
      if smallNum limits.arch64Bit n then 0 else bignumSize limits.arch64Bit n
  | [.codePtr _] => 0
  | [.refPtr _ address] =>
      match h : sptLookup address refs with
      | none => 0
      | some (.byteArray _ bytes) =>
          bytes.length / (archSize limits / 8) + 2
      | some (.valueArray vals) =>
          approxOf limits vals (sptDelete address refs) + vals.length + 1
      | some (.thunk _ value) =>
          approxOf limits [value] (sptDelete address refs) + 2
      | some (.mutBlock _ _ left current right) =>
          approxOf limits (left ++ [current] ++ right) (sptDelete address refs) +
            left.length + right.length + 2
  | [.block _ _ []] => 0
  | [.block _ _ vals] =>
      approxOf limits vals refs + vals.length + 1
termination_by (sptSize refs, sizeOf values)
decreasing_by
  all_goals simp_wf
  all_goals
    try
      apply Prod.Lex.right
      omega
  all_goals
    try
      apply Prod.Lex.left
      apply sptSize_delete_lt
      simp_all
  apply Prod.Lex.right
  have hy : 0 < sizeOf y := by cases y <;> simp_wf <;> omega
  omega

end Flapjack.Compiler.Backend.DataProps
