import Flapjack.Compiler.Backend.SourceToFlat.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.SourceLet.Proofs.Semantics
import Flapjack.Compiler.Backend.SourceToSource

/-! Compose source let-lifting with the factored source-to-flat simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticsHOL

/-- Under source non-failure, preprocessing preserves every clock-indexed
observation, including failure observations. This is Flapjack composition
infrastructure; it is not a separate HOL theorem port. -/
theorem sourcePreprocessing_semantics {F : Type} (state : State F) (env : SemEnv Value)
    (program : List Dec) (outcome : HolBehaviour)
    (safe : ¬ semanticsProg state env program .fail) :
    semanticsProg state env (SourceToSource.compile program) outcome ↔
      semanticsProg state env program outcome := by
  have observations := SourceLet.compileDecs_clock_observations state env program safe
  cases outcome <;> simp only [SourceToSource.compile, semanticsProg, observations]

/-- The checked source preprocessing and full source-to-flat pass preserve
the original program's observations under the existing factored pass
precondition. The relation and whole-pass correspondence still require HOL
review; this theorem introduces no additional cross-language claim. -/
theorem factoredCakeCompile_semantics {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (targetConfig : FlatSem.InstallConfig C) (decs : List Dec)
    (precondition : FactoredPrecondition interp transform source sourceEnv config targetConfig
      (SourceToSource.compile decs))
    (safe : ¬ semanticsProg source sourceEnv decs .fail) :
    semanticsProg source sourceEnv decs
      (FlatSem.semantics targetConfig source.ffi (compileTotal config (SourceToSource.compile decs)).2) := by
  have sourceSafe : ¬ semanticsProg source sourceEnv (SourceToSource.compile decs) .fail := by
    intro fails
    exact safe ((sourcePreprocessing_semantics source sourceEnv decs .fail safe).mp fails)
  apply (sourcePreprocessing_semantics source sourceEnv decs _ safe).mp
  exact factoredCompile_semantics interp transform source sourceEnv config targetConfig
    (SourceToSource.compile decs) precondition sourceSafe

end Flapjack.Compiler.Backend.SourceToFlat
