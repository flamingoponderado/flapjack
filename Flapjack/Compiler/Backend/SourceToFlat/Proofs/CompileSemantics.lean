import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocal
import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatElim.Proofs.Removal
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ProgramSimulation

/-!
Composition of the source-to-flat program simulation with flat elimination and
pattern compilation. The factored lemmas are proof infrastructure; the final
`sourceCompile_semantics` theorem has been compared with its HOL counterpart.
-/
namespace Flapjack.Compiler.Backend.SourceToFlat

open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Flat elimination and pattern compilation preserve non-failing behavior
under the pattern pass's installation-configuration relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_flat_correct"]
theorem factoredCompileFlat_semantics {C F : Type}
    (cfg : FlatPattern.Config) (ffi : HolFfiState F) (program : List FlatLang.Exp)
    (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (premises : FlatPattern.installConfRel cfg sourceConfig targetConfig ∧
      FlatSem.semantics sourceConfig ffi program ≠ .fail) :
    FlatSem.semantics sourceConfig ffi program =
      FlatSem.semantics targetConfig ffi (compileFlatTotal cfg program) := by
  obtain ⟨related, safe⟩ := premises
  have elim := FlatElim.flat_remove_semantics sourceConfig ffi program safe
  have elimSafe : FlatSem.semantics sourceConfig ffi (FlatElim.removeFlatProgTotal program) ≠ .fail := by
    rw [← elim]
    exact safe
  have pattern := FlatPattern.compileDecs_semantics cfg cfg ffi
    (FlatElim.removeFlatProgTotal program) sourceConfig targetConfig related elimSafe
  simpa [compileFlatTotal] using elim.trans pattern

/-- Whole-pass precondition in the source's existential shape. The initial
environment's value type is independent of both compiler and FFI types. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "precondition_def"]
def SourcePrecondition {C F A : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C)))
    (source : State F) (sourceEnv : SemEnv A) (config : Config)
    (targetConfig : FlatSem.InstallConfig C) (decs : List Dec) : Prop :=
  ∃ middleConfig transform,
    FactoredPrecondition1 interp transform source sourceEnv config middleConfig decs ∧
      FlatPattern.installConfRel config.patternCfg middleConfig targetConfig

/-- Source-to-flat behavior under the original precondition and absence of
source failure. The primitive floating-point model inherits the documented
rational-cut assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_semantics"]
theorem sourceCompile_semantics {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C)))
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (targetConfig : FlatSem.InstallConfig C) (decs : List Dec)
    (precondition : SourcePrecondition interp source sourceEnv config targetConfig decs)
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs
      (FlatSem.semantics targetConfig source.ffi (compileTotal config decs).2) := by
  obtain ⟨middleConfig, transform, initial, related⟩ := precondition
  generalize compiled : compileProg config decs = pair
  obtain ⟨nextConfig, code⟩ := pair
  have cfgEq : nextConfig.patternCfg = config.patternCfg := by
    have h : (compileProg config decs).1.patternCfg = config.patternCfg := by simp only [compileProg]
    simpa [compiled] using h
  have noFail := factoredCompileProg_semantics_ne_fail interp transform source sourceEnv config nextConfig
    middleConfig decs code initial compiled safe
  have relation : FlatPattern.installConfRel nextConfig.patternCfg middleConfig targetConfig := by
    simpa [cfgEq] using related
  have passes := factoredCompileFlat_semantics nextConfig.patternCfg source.ffi code middleConfig targetConfig ⟨relation, noFail⟩
  have initialSem := factoredCompileProg_semantics interp transform source sourceEnv config
    middleConfig decs initial safe
  simp only [compiled] at initialSem
  rw [passes] at initialSem
  simpa [compileTotal, compiled] using initialSem


end Flapjack.Compiler.Backend.SourceToFlat
