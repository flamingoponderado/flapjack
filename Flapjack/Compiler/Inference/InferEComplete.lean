module

public import Flapjack.Compiler.Inference.EnvRel

@[expose] public section

/-! Prerequisites for inference completeness on expressions. -/
namespace Flapjack.Compiler.Inference.InferEComplete
open Flapjack.Compiler.Inference.EnvRel Flapjack.Compiler.Inference.InferProps

/-- Closed inference types are equal when their declarative conversions agree. -/
@[hol "cakeml/compiler/inference/proofs/infer_eCompleteScript.sml" "convert_bi_remove"]
theorem convertBiRemove (a b : InferT) (n m : Nat) :
    convertT a = convertT b ∧ Infer.checkT n (fun _ => False) a ∧
      Infer.checkT m (fun _ => False) b → a = b := by
  rintro ⟨equal, checkedA, checkedB⟩
  have converted := congrArg unconvertT equal
  rw [checkTEmptyUnconvertConvertId a n checkedA,
      checkTEmptyUnconvertConvertId b m checkedB] at converted
  exact converted
end Flapjack.Compiler.Inference.InferEComplete
