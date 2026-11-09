import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingConstructors

/-! Growing expression simulation in a local environment. These factored
relations and this composition lemma are not yet reviewed HOL ports. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A growing expression step with an explicit flat local environment. -/
def LocalExpressionStep {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN)
    (compMap : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp) : Prop :=
  let result := EvaluateHOL.evaluate source sourceEnv [expr]
  let flatResult := FlatSem.evaluate flatEnv flat [compileExp trace compMap expr]
  ∃ nextGenv, ExprSim nextGenv compMap trace sourceEnv flatEnv source flat expr ∧
    match result.2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other) result.1 flatResult.1 ∧
        envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState

end Flapjack.Compiler.Backend.SourceToFlat
