import Flapjack.HolRef

/-! CakeML's inference type carrier. -/
namespace Flapjack.Compiler.Inference

/-- Unification variables, de Bruijn variables, and numbered type constructors. -/
@[hol "cakeml/compiler/inference/infer_tScript.sml" "infer_t"]
inductive InferT where
  | varDb : Nat → InferT
  | app : List InferT → Nat → InferT
  | uvar : Nat → InferT
  deriving BEq, Repr

end Flapjack.Compiler.Inference
