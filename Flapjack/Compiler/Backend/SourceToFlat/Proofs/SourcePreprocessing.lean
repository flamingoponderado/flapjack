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

end Flapjack.Compiler.Backend.SourceToFlat
