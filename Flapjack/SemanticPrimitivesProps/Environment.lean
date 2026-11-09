import Flapjack.HolRef
import Flapjack.SemanticPrimitivesHOL.Control

/-! Properties of source declaration environments. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- Declaration environment extension is associative. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "extend_dec_env_assoc"]
theorem extendDecEnv_assoc (inner middle outer : SemEnv Value) :
    extendDecEnv inner (extendDecEnv middle outer) = extendDecEnv (extendDecEnv inner middle) outer := by
  cases inner with
  | mk iv ic =>
    cases middle with
    | mk mv mc =>
      cases outer with
      | mk ov oc =>
        cases iv; cases ic; cases mv; cases mc; cases ov; cases oc
        simp [extendDecEnv, nsAppend, List.append_assoc]

end Flapjack.SemanticPrimitivesProps
