module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentBind
public import Flapjack.Compiler.Backend.SourceEval.Proofs.ValueRelation
public import Flapjack.SemanticPrimitivesProps.RecursiveFunctions
public import Flapjack.SemanticPrimitivesProps.OpApp

@[expose] public section

/-! Recursive environments and closure application preserve source value relations. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Flapjack infrastructure: HOL inlines recursive-environment merging and binding preservation in its evaluator simulation cases. -/
theorem envRel_buildRecEnv (es : EvalOracleState) (env env' cl cl' : SemEnv Value)
    (ev ev' : Namespace ModN VarN Value) (funs : List (VarN × VarN × Flapjack.AstHOL.Exp))
    (premises : envRel (ValueRel es) { env with v := ev } { env' with v := ev' } ∧
      envRel (ValueRel es) cl cl') :
    envRel (ValueRel es) { env with v := buildRecEnv funs cl ev }
      { env' with v := buildRecEnv funs cl' ev' } := by
  obtain ⟨baseRel, closureRel⟩ := premises
  have bindingsRel : ∀ xs : List (VarN × VarN × Flapjack.AstHOL.Exp),
      List.Forall₂ (Flapjack.holRprod (· = ·) (ValueRel es))
        (xs.map fun (f, _, _) => (f, Value.recclosure cl funs f))
        (xs.map fun (f, _, _) => (f, Value.recclosure cl' funs f)) := by
    intro xs
    induction xs with
    | nil => exact .nil
    | cons item rest ih =>
      obtain ⟨name, arg, exp⟩ := item
      exact .cons ⟨rfl, .recclosure ((valueEnvRel_iff _ _ _).mpr closureRel)⟩ ih
  rw [buildRecEnv_merge funs () cl ev, buildRecEnv_merge funs () cl' ev']
  rw [nsAppend_to_nsBindList, nsAppend_to_nsBindList]
  exact envRel_add_nsBindList _ env ev env' ev' _ _ ⟨baseRel, bindingsRel funs⟩

/-- Flapjack infrastructure: HOL proves closure and recursive-closure application preservation inline in the application simulation case. -/
theorem doOpApp_related (oracle : EvalOracleState) (source target : List Value)
    (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp)
    (values : List.Forall₂ (ValueRel oracle) source target)
    (run : doOpApp source = some (callEnv, body)) :
    ∃ callEnv', doOpApp target = some (callEnv', body) ∧
      envRel (ValueRel oracle) callEnv callEnv' := by
  rcases (doOpApp_cases callEnv source body).mp run with closure | recursive
  · obtain ⟨arg, env, name, exp, rfl, rfl, rfl⟩ := closure
    cases values with
    | cons funRel tail =>
      cases tail with
      | @cons _ arg' _ _ argRel tail =>
        cases tail
        cases funRel with
        | @closure _ env' _ _ envRel' =>
          refine ⟨{ env' with v := nsBind name arg' env'.v }, ?_, ?_⟩
          · simp [doOpApp]
          · apply envRel_add_nsBind (ValueRel oracle)
            exact ⟨(valueEnvRel_iff _ _ _).mp envRel', argRel⟩
  · obtain ⟨arg, env, funs, name, param, exp, rfl, found, distinct, rfl, rfl⟩ := recursive
    cases values with
    | cons funRel tail =>
      cases tail with
      | @cons _ arg' _ _ argRel tail =>
        cases tail
        cases funRel with
        | @recclosure _ env' _ _ envRel' =>
          refine ⟨{ env' with v := nsBind param arg' (buildRecEnv funs env' env'.v) }, ?_, ?_⟩
          · simp [doOpApp, found, distinct]
          · apply envRel_add_nsBind (ValueRel oracle)
            constructor
            · apply envRel_buildRecEnv
              exact ⟨(valueEnvRel_iff _ _ _).mp envRel', (valueEnvRel_iff _ _ _).mp envRel'⟩
            · exact argRel

end Flapjack.Compiler.Backend.SourceEval.Proofs
