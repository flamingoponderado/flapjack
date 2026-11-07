import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentBind
import Flapjack.Compiler.Backend.SourceEval.Proofs.ValueRelation
import Flapjack.SemanticPrimitivesProps.RecursiveFunctions

/-! Recursive environments preserve source value relations. -/
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

end Flapjack.Compiler.Backend.SourceEval.Proofs
