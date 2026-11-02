import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact

/-! The flat pattern-match evaluator used by the source-to-flat proof. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.SemanticPrimitivesHOL

/-- Evaluate the selected flat match row or return the corresponding match error. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_match_def"]
noncomputable def evaluateMatch {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (value : FlatSem.Value)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (errorValue : FlatSem.Value) : FlatSem.EvalResult C F :=
  match FlatSem.pmatchRows rows state value with
  | .typeError => (state, .err (.abort .typeError))
  | .noMatch => (state, .err (.raise errorValue))
  | .match (bindings, pattern, body) =>
    if (FlatLang.patBindings pattern).Nodup then
      FlatSem.evaluate { env with v := bindings ++ env.v } state [body]
    else (state, .err (.abort .typeError))

end Flapjack.Compiler.Backend.FlatProps
