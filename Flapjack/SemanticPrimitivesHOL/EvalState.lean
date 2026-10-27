import Flapjack.SemanticPrimitivesHOL.Conversions

/-! Source Eval environment-generation bookkeeping. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "lookup_env_def"]
def lookupEnv (state : EvalOracleState) (id : Nat × Nat) : Option (SemEnv Value) := do
  let generation ← state.envs[id.1]?
  generation[id.2]?

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "add_decs_generation_def"]
def addDecsGeneration (state : EvalDecsState) : EvalDecsState :=
  let (_, _, nextGeneration) := state.envIdCounter
  { state with envIdCounter := (nextGeneration, 0, nextGeneration + 1) }

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "add_env_generation_def"]
def addEnvGeneration (state : EvalOracleState) : EvalOracleState :=
  { state with generation := state.envs.length, envs := state.envs ++ [[]] }

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "declare_env_def"]
def declareEnv (state : Option EvalState) (env : SemEnv Value) : Option (Value × Option EvalState) :=
  match state with
  | none => none
  | some (.evalDecs state) =>
    let (generation, nextId, nextGeneration) := state.envIdCounter
    some (.env env (generation, nextId),
      some (.evalDecs { state with envIdCounter := (generation, nextId + 1, nextGeneration) }))
  | some (.evalOracle state) => do
    let generation ← state.envs[state.generation]?
    let value := Value.conv none [natToValue state.generation, natToValue generation.length]
    let state := { state with envs := state.envs.set state.generation (generation ++ [env]) }
    some (value, some (.evalOracle state))

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "reset_env_generation_def"]
def resetEnvGeneration (prior current : Option EvalState) : Option EvalState :=
  match prior, current with
  | some (.evalDecs before), some (.evalDecs after) =>
    let (generation, nextId, _) := before.envIdCounter
    let (_, _, nextGeneration) := after.envIdCounter
    some (.evalDecs { after with envIdCounter := (generation, nextId, nextGeneration) })
  | some (.evalOracle before), some (.evalOracle after) =>
    some (.evalOracle { after with generation := before.generation })
  | _, _ => current

end Flapjack.SemanticPrimitivesHOL
