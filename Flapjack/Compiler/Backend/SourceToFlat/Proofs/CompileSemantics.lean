import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocal
import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatElim.Proofs.Removal
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ProgramSimulation

/-!
Composition of the source-to-flat program simulation with flat elimination and
pattern compilation. The component simulations use preliminary factored
relations; this is not yet a reviewed port of the original HOL theorem.
-/
namespace Flapjack.Compiler.Backend.SourceToFlat

open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- The declaration compiler updates indices and environments, while preserving
the pattern compiler configuration. -/
theorem compileProg_patternCfg (config : Config) (decs : List Dec) :
    (compileProg config decs).1.patternCfg = config.patternCfg := by
  simp only [compileProg]

/-- Flat elimination and pattern compilation preserve non-failing behavior
under the pattern pass's installation-configuration relation. -/
theorem factoredCompileFlat_semantics {C F : Type}
    (cfg : FlatPattern.Config) (ffi : HolFfiState F) (program : List FlatLang.Exp)
    (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (related : FlatPattern.installConfRel cfg sourceConfig targetConfig)
    (safe : FlatSem.semantics sourceConfig ffi program ≠ .fail) :
    FlatSem.semantics sourceConfig ffi program =
      FlatSem.semantics targetConfig ffi (compileFlatTotal cfg program) := by
  have elim := FlatElim.flat_remove_semantics ffi program sourceConfig safe
  have elimSafe : FlatSem.semantics sourceConfig ffi (FlatElim.removeFlatProgTotal program) ≠ .fail := by
    rw [← elim]
    exact safe
  have pattern := FlatPattern.compileDecs_semantics_proofSide cfg cfg ffi
    (FlatElim.removeFlatProgTotal program) sourceConfig targetConfig related elimSafe
  simpa [compileFlatTotal] using elim.trans pattern

/-- Preliminary whole-pass precondition: the source program precondition and
the pattern compiler's installation relation hold for the same intermediate
flat configuration. -/
def FactoredPrecondition {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (targetConfig : FlatSem.InstallConfig C) (decs : List Dec) : Prop :=
  ∃ middleConfig, FactoredPrecondition1 interp transform source sourceEnv config middleConfig decs ∧
    FlatPattern.installConfRel config.patternCfg middleConfig targetConfig

/-- Every behavior of the full source-to-flat compilation is a source program
behavior, under the factored precondition and component relations. Their
cross-language correspondence remains a separate review obligation. -/
theorem factoredCompile_semantics {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (targetConfig : FlatSem.InstallConfig C) (decs : List Dec)
    (precondition : FactoredPrecondition interp transform source sourceEnv config targetConfig decs)
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs
      (FlatSem.semantics targetConfig source.ffi (compileTotal config decs).2) := by
  obtain ⟨middleConfig, initial, related⟩ := precondition
  generalize compiled : compileProg config decs = pair
  obtain ⟨nextConfig, code⟩ := pair
  have cfgEq : nextConfig.patternCfg = config.patternCfg := by
    have h := compileProg_patternCfg config decs
    simpa [compiled] using h
  have noFail := factoredCompileProg_semantics_ne_fail interp transform source sourceEnv config nextConfig
    middleConfig decs code initial compiled safe
  have relation : FlatPattern.installConfRel nextConfig.patternCfg middleConfig targetConfig := by
    simpa [cfgEq] using related
  have passes := factoredCompileFlat_semantics nextConfig.patternCfg source.ffi code middleConfig targetConfig relation noFail
  have initialSem := factoredCompileProg_semantics interp transform source sourceEnv config nextConfig
    middleConfig decs code initial compiled safe
  rw [passes] at initialSem
  simpa [compileTotal, compiled] using initialSem

/-- Whole-pass precondition in the source's existential shape. The initial
environment's value type is independent of both compiler and FFI types. This
is not yet tagged as the HOL definition: the pattern installation relation
and its compiler dependencies still require source correspondence review. -/
def SourcePrecondition {C F A : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C)))
    (source : State F) (sourceEnv : SemEnv A) (config : Config)
    (targetConfig : FlatSem.InstallConfig C) (decs : List Dec) : Prop :=
  ∃ middleConfig transform,
    FactoredPrecondition1 interp transform source sourceEnv config middleConfig decs ∧
      FlatPattern.installConfRel config.patternCfg middleConfig targetConfig

/-- The explicit transformation used in the factored proof is a witness for
the source's existential precondition. -/
theorem sourcePrecondition_iff {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C)))
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (targetConfig : FlatSem.InstallConfig C) (decs : List Dec) :
    SourcePrecondition interp source sourceEnv config targetConfig decs ↔
      ∃ transform, FactoredPrecondition interp transform source sourceEnv config targetConfig decs := by
  constructor
  · rintro ⟨middle, transform, initial, related⟩
    exact ⟨transform, middle, initial, related⟩
  · rintro ⟨transform, middle, initial, related⟩
    exact ⟨middle, transform, initial, related⟩

/-- Full source-to-flat behavior in the original existential-precondition
shape. The component simulation relations remain under HOL correspondence
review, so this is not yet tagged as the source correctness theorem. -/
theorem sourceCompile_semantics {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C)))
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (targetConfig : FlatSem.InstallConfig C) (decs : List Dec)
    (precondition : SourcePrecondition interp source sourceEnv config targetConfig decs)
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs
      (FlatSem.semantics targetConfig source.ffi (compileTotal config decs).2) := by
  obtain ⟨transform, factored⟩ := (sourcePrecondition_iff interp source sourceEnv config targetConfig decs).mp precondition
  exact factoredCompile_semantics interp transform source sourceEnv config targetConfig decs factored safe

end Flapjack.Compiler.Backend.SourceToFlat
