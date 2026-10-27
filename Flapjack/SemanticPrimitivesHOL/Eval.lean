import Flapjack.SemanticPrimitivesHOL.Concrete
import Flapjack.SemanticPrimitivesHOL.Conversions
import Flapjack.SemanticPrimitivesHOL.EvalState

/-! Proof-side dynamic compilation semantics. The equality of arbitrary source
values uses Lean's classical decision procedure, so `doEval` is noncomputable;
it is not the executable compiler path. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "compiler_agrees_def"]
def compilerAgrees (compiler : CompilerFun) (args : CompilerArgs)
    (outputs : Value × Value × Value) : Prop :=
  let (stateValue, bytesValue, wordsValue) := outputs
  match compiler args, args, valueToWord8List bytesValue, valueToWord64List wordsValue with
  | some (state, compilerBytes, compilerWords), (_, previous, _), some bytes, some words =>
    state = stateValue ∧ compilerBytes = bytes ∧ compilerWords = words ∧
      concreteValue stateValue = true ∧ concreteValue previous = true
  | _, _, _, _ => False

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_eval_def"]
noncomputable def doEval (values : List Value) (evalState : Option EvalState) :
    Option (SemEnv Value × List AstHOL.Dec × Option EvalState) := by
  classical
  exact match evalState, values with
    | some (.evalDecs state), [.env env id, previous, encodedDecs, next, bytes, words] =>
      match state.decodeDecs encodedDecs with
      | none => none
      | some decs =>
        if previous = state.compilerState ∧ concreteValue encodedDecs = true ∧
            compilerAgrees state.compiler (id, previous, decs) (next, bytes, words) then
          some (env, decs, some (.evalDecs (addDecsGeneration { state with compilerState := next })))
        else none
    | some (.evalOracle state), values =>
      match state.customDoEval values state.oracle with
      | none => none
      | some (id, oracle, decs) =>
        match lookupEnv state id with
        | none => none
        | some env => some (env, decs, some (.evalOracle (addEnvGeneration { state with oracle := oracle })))
    | _, _ => none

end Flapjack.SemanticPrimitivesHOL
