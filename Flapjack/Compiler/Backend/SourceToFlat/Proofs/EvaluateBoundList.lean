module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingNamedLet
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MemoryOps
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.Equality
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveTest

@[expose] public section

/-! Growing argument lists in local environments using the reviewed relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Abort-sensitive growing simulation for a local expression list. -/
def LocalExpressionListStep {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (args : List AstHOL.Exp) : Prop :=
  let sourceResult := EvaluateHOL.evaluate source sourceEnv args
  let flatResult := FlatSem.evaluate flatEnv flat (compileExps trace compMap args)
  ∃ nextGenv, ExprListSim nextGenv compMap trace sourceEnv flatEnv source flat args ∧
    match sourceResult.2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other) sourceResult.1 flatResult.1 ∧
        envGenRel gen sourceResult.1.evalState ∧ oracForwardRel interp source.evalState sourceResult.1.evalState

/-- Unfold the source evaluator on two or more expressions for simulation.
This convenience equation has no separate HOL declaration. -/
theorem sourceEvaluate_cons {F : Type} (source : State F) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp) :
    EvaluateHOL.evaluate source env (first :: second :: rest) =
      let head := EvaluateHOL.evaluate source env [first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := EvaluateHOL.evaluate head.1 env (second :: rest)
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (EvaluateHOL.headValue values :: values')) := by
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source env [first] []).1]
  rfl

end Flapjack.Compiler.Backend.SourceToFlat
