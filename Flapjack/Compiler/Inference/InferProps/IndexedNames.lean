module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.Misc.FindIndex

@[expose] public section

/-! Lookup in indexed name lists used by inference proofs. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack Flapjack.Misc Flapjack.Basis.Pure.MlString

/-- First-match lookup in a name list zipped with consecutive indices. This is shared Flapjack proof infrastructure. -/
theorem lookupIndexed (names : List MlString) (key : MlString) (offset : Nat) :
    (names.zip ((List.range' offset names.length).map InferT.varDb)).lookup key =
      (findIndex key names offset).map InferT.varDb := by
  induction names generalizing offset with
  | nil => rfl
  | cons name names ih =>
    by_cases same : name = key
    · subst key; simp [findIndex, List.range']
    · have different : (key == name) = false := by simp [Ne.symm same]
      simpa [findIndex, same, List.range', List.lookup, different] using ih (offset + 1)
/-- The zero-offset instance used by inference type substitutions. -/
theorem lookupIndex0 (names : List MlString) (key : MlString) :
    (names.zip ((List.range names.length).map InferT.varDb)).lookup key =
      (findIndex key names 0).map InferT.varDb := by
  simpa [List.range_eq_range'] using lookupIndexed names key 0

end Flapjack.Compiler.Inference.InferProps
