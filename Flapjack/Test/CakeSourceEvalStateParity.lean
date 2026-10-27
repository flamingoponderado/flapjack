import Flapjack.SemanticPrimitivesHOL.EvalState

/-! Eval environment-generation observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceEvalStateParity
open Flapjack.SemanticPrimitivesHOL

private def emptyEnv : SemEnv Value := ⟨.bind [] [], .bind [] []⟩
private def decs : EvalDecsState :=
  { compiler := fun _ => none, compilerState := .litv (.intLit 0),
    envIdCounter := (2, 3, 9), decodeDecs := fun _ => none }
private def oracle : EvalOracleState :=
  { oracle := fun _ => ((0, 0), .litv (.intLit 0), []), customDoEval := fun _ _ => none,
    envs := [[emptyEnv]], generation := 0 }

#guard (addDecsGeneration decs).envIdCounter = (9, 0, 10)
#guard let state := addEnvGeneration { oracle with envs := [[], []], generation := 8 }
  state.generation == 2 && state.envs.length == 3
#guard (lookupEnv oracle (0, 0)).isSome
#guard (lookupEnv oracle (1, 0)).isNone
#guard match declareEnv (some (.evalDecs decs)) emptyEnv with
  | some (.env _ (2, 3), some (.evalDecs state)) => state.envIdCounter == (2, 4, 9)
  | _ => false
#guard (declareEnv (some (.evalOracle { oracle with generation := 1 })) emptyEnv).isNone
#guard match declareEnv (some (.evalOracle oracle)) emptyEnv with
  | some (.conv none [.litv (.intLit 0), .litv (.intLit 1)], some (.evalOracle state)) =>
      (state.envs[0]?).map List.length == some 2
  | _ => false
#guard match resetEnvGeneration (some (.evalDecs decs))
    (some (.evalDecs { decs with envIdCounter := (4, 5, 11) })) with
  | some (.evalDecs state) => state.envIdCounter == (2, 3, 11)
  | _ => false

end Flapjack.Test.CakeSourceEvalStateParity
