import Flapjack.EvaluateHOL

/-! Proof-side Eval observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceEvalParity
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

private def emptyEnv : SemEnv Value := ⟨.bind [] [], .bind [] []⟩
private def intV (n : Int) : Value := .litv (.intLit n)
private def decs : EvalDecsState :=
  { compiler := fun _ => some (intV 2, [], []), compilerState := intV 1,
    envIdCounter := (2, 3, 9), decodeDecs := fun _ => some [] }
private def oracle : EvalOracleState :=
  { oracle := fun _ => ((0, 0), intV 0, []), customDoEval := fun _ oc => some ((0, 0), oc, []),
    envs := [[emptyEnv]], generation := 0 }
private def inputs (previous : Value) : List Value :=
  [.env emptyEnv (2, 3), previous, intV 0, intV 2, listToValue [], listToValue []]

example : (doEval [] none).isNone = true := by rfl

example : (match doEval [] (some (.evalOracle oracle)) with
  | some (_, ds, some (.evalOracle state)) => ds.length == 0 && state.generation == 1 && state.envs.length == 2
  | _ => false) = true := by rfl

example : (match doEval (inputs (intV 1)) (some (.evalDecs decs)) with
  | some (_, ds, some (.evalDecs state)) => ds.length == 0 && state.envIdCounter == (9, 0, 10)
  | _ => false) = true := by
  simp [doEval, inputs, decs, compilerAgrees, intV, concreteValue, valueToWord8List,
    valueToWord64List, valueToList, listToValue, listTypeNum, maybeAllList, addDecsGeneration]

example : (doEval (inputs (intV 3)) (some (.evalDecs decs))).isNone = true := by
  simp [doEval, inputs, decs, intV]

example (state : State Nat) : (match (doEvalRes [] { state with evalState := none } :
    State Nat × Result (SemEnv Value × List AstHOL.Dec) Bool).2 with
  | .err (.abort .typeError) => true
  | _ => false) = true := by rfl

end Flapjack.Test.CakeSourceEvalParity
