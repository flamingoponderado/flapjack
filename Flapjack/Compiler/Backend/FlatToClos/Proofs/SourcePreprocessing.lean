import Flapjack.Compiler.Backend.FlatToClos.Proofs.Semantics
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.SourcePreprocessing
import Flapjack.Compiler.Backend.SourceToFlat.ToClos

/-! Source preprocessing composed with the existing flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- The source-to-source pass followed by source-to-flat and flat-to-closure
compilation produces an observable behavior of the original source program,
under the existing factored pass and incremental-compiler assumptions. This
is Flapjack composition infrastructure: the component relations and their
HOL correspondence remain open, as do the later backend passes. -/
theorem cakeCompileProg_semantics_proofSide {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (SourceToFlat.Config × C)))
    (transform : List AstHOL.Dec → List AstHOL.Dec)
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig C) (compiler : ClosSem.Compiler C)
    (declarations : List AstHOL.Dec) (maxApp : Nat)
    (precondition : SourceToFlat.FactoredPrecondition interp transform source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs compiler) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty
        (pureCo incCompileDecs ∘ flatConfig.compileOracle) compiler
        (compileProg (SourceToFlat.compileTotal sourceConfig (SourceToSource.compile declarations)).2)) := by
  have sourceSafe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv
      (SourceToSource.compile declarations) .fail := by
    intro fails
    exact safe ((SourceToFlat.sourcePreprocessing_semantics source sourceEnv declarations .fail safe).mp fails)
  apply (SourceToFlat.sourcePreprocessing_semantics source sourceEnv declarations _ safe).mp
  exact sourceCompileProg_semantics_proofSide interp transform source sourceEnv sourceConfig flatConfig compiler
    (SourceToSource.compile declarations) maxApp precondition sourceSafe positive production

/-- The same conditional simulation applies to code returned by the
executable source-to-closure entry point. Its output equality is established
by unfolding the actual composition; the simulation assumptions remain those
of `cakeCompileProg_semantics_proofSide`. -/
theorem cakeCompileToClosFuel_semantics_proofSide {C F : Type} [Nonempty C]
    (fuel : Nat) (interp : Option (Value → Option (SourceToFlat.Config × C)))
    (transform : List AstHOL.Dec → List AstHOL.Dec)
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig nextConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig C) (compiler : ClosSem.Compiler C)
    (declarations : List AstHOL.Dec) (program : List ClosLang.Exp) (maxApp : Nat)
    (precondition : SourceToFlat.FactoredPrecondition interp transform source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs compiler)
    (run : SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (nextConfig, program)) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty
        (pureCo incCompileDecs ∘ flatConfig.compileOracle) compiler program) := by
  have output := congrArg (Option.map Prod.snd) run
  have same : compileProg (SourceToFlat.compileTotal sourceConfig (SourceToSource.compile declarations)).2 = program := by
    apply Option.some.inj
    simpa [SourceToFlat.compileCakeToClosFuel, SourceToFlat.compileToClosFuel, SourceToFlat.compile] using output
  rw [← same]
  exact cakeCompileProg_semantics_proofSide interp transform source sourceEnv sourceConfig flatConfig compiler
    declarations maxApp precondition safe positive production

/-- Source preprocessing and the executable source-to-closure pass preserve
behavior under the source pass's existential precondition. This composition
still depends on the stated closure compiler and positivity conditions. -/
theorem cakeCompileToClosFuel_semantics_exists {C F : Type} [Nonempty C]
    (fuel : Nat) (interp : Option (Value → Option (SourceToFlat.Config × C)))
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig nextConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig C) (compiler : ClosSem.Compiler C)
    (declarations : List AstHOL.Dec) (program : List ClosLang.Exp) (maxApp : Nat)
    (precondition : SourceToFlat.SourcePrecondition interp source sourceEnv sourceConfig
      flatConfig (SourceToSource.compile declarations))
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < maxApp)
    (production : flatConfig.compile = pureCc incCompileDecs compiler)
    (run : SourceToFlat.compileCakeToClosFuel fuel sourceConfig declarations = some (nextConfig, program)) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations
      (ClosSem.semantics source.ffi maxApp HolFiniteMapExact.empty
        (pureCo incCompileDecs ∘ flatConfig.compileOracle) compiler program) := by
  obtain ⟨transform, factored⟩ :=
    (SourceToFlat.sourcePrecondition_iff interp source sourceEnv sourceConfig flatConfig
      (SourceToSource.compile declarations)).mp precondition
  exact cakeCompileToClosFuel_semantics_proofSide fuel interp transform source sourceEnv sourceConfig
    nextConfig flatConfig compiler declarations program maxApp factored safe positive production run

end Flapjack.Compiler.Backend.FlatToClos
