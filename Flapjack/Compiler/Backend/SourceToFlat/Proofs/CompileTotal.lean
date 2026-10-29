import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatElim.Proofs.Reachability
import Flapjack.Compiler.Backend.FlatElim.Proofs.Removal
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ProgramSimulation
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocal

/-! Totality of the bounded source-to-flat pipeline. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- The compatibility entry point returns the total source-to-flat result. -/
theorem compile_succeeds (config : Config) (decs : List Flapjack.AstHOL.Dec) :
    ∃ result, compile config decs = some result := ⟨compileTotal config decs, rfl⟩

/-- The total production pipeline applies pattern compilation to the
source-shaped elimination closure. -/
theorem compileFlatTotal_eq_closure (cfg : FlatPattern.Config) (code : List FlatLang.Exp) :
    compileFlatTotal cfg code =
      (if code.any FlatElim.hasEvalDec then code else
        let (roots, tree) := FlatElim.analyseCode code
        FlatElim.removeUnreachable (FlatElim.closure roots tree) code).map (FlatPattern.compileDec cfg) := by
  simp only [compileFlatTotal, FlatElim.removeFlatProgTotal_eq]

/-- Pattern compilation preserves proof-side observations of the program
that flat elimination produces. This does not establish correctness of flat
elimination or correspondence of the proof-side semantics with HOL. -/
theorem compileFlatTotal_pattern_semantics {C F : Type}
    (cfg relationCfg : FlatPattern.Config) (ffi : HolFfiState F)
    (code : List FlatLang.Exp) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : FlatPattern.installConfRel relationCfg sourceConfig targetConfig)
    (notFail : FlatSem.semantics sourceConfig ffi (FlatElim.removeFlatProgTotal code) ≠ .fail) :
    FlatSem.semantics sourceConfig ffi (FlatElim.removeFlatProgTotal code) =
      FlatSem.semantics targetConfig ffi (compileFlatTotal cfg code) := by
  exact FlatPattern.compileDecs_semantics_proofSide relationCfg cfg ffi _ _ _ configs notFail

/-- The normal source-to-flat entry point preserves proof-side observations
from the output of elimination through its pattern-compilation stage. -/
theorem compileTotal_pattern_semantics {C F : Type}
    (config : Config) (decs : List Flapjack.AstHOL.Dec)
    (relationCfg : FlatPattern.Config) (ffi : HolFfiState F)
    (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : FlatPattern.installConfRel relationCfg sourceConfig targetConfig)
    (notFail : FlatSem.semantics sourceConfig ffi
      (FlatElim.removeFlatProgTotal (compileProg config decs).2) ≠ .fail) :
    FlatSem.semantics sourceConfig ffi (FlatElim.removeFlatProgTotal (compileProg config decs).2) =
      FlatSem.semantics targetConfig ffi (compileTotal config decs).2 := by
  exact compileFlatTotal_pattern_semantics (compileProg config decs).1.patternCfg
    relationCfg ffi _ _ _ configs notFail

/-- Flat elimination followed by pattern compilation preserves proof-side
observations. The constituent semantics and relations still require HOL
correspondence review. -/
theorem compileFlatTotal_semantics_proofSide {C F : Type}
    (cfg relationCfg : FlatPattern.Config) (ffi : HolFfiState F)
    (code : List FlatLang.Exp) (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : FlatPattern.installConfRel relationCfg sourceConfig targetConfig)
    (notFail : FlatSem.semantics sourceConfig ffi code ≠ .fail) :
    FlatSem.semantics sourceConfig ffi code =
      FlatSem.semantics targetConfig ffi (compileFlatTotal cfg code) := by
  have eliminated := FlatElim.flat_remove_semantics ffi code sourceConfig notFail
  have eliminatedNotFail : FlatSem.semantics sourceConfig ffi (FlatElim.removeFlatProgTotal code) ≠ .fail := by
    rw [← eliminated]
    exact notFail
  exact eliminated.trans (compileFlatTotal_pattern_semantics cfg relationCfg ffi code
    sourceConfig targetConfig configs eliminatedNotFail)

/-- The normal production entry point preserves proof-side observations
from the output of source lowering through elimination and pattern compilation.
Correctness of source lowering and HOL correspondence remain separate. -/
theorem compileTotal_flat_semantics_proofSide {C F : Type}
    (config : Config) (decs : List Flapjack.AstHOL.Dec)
    (relationCfg : FlatPattern.Config) (ffi : HolFfiState F)
    (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : FlatPattern.installConfRel relationCfg sourceConfig targetConfig)
    (notFail : FlatSem.semantics sourceConfig ffi (compileProg config decs).2 ≠ .fail) :
    FlatSem.semantics sourceConfig ffi (compileProg config decs).2 =
      FlatSem.semantics targetConfig ffi (compileTotal config decs).2 := by
  exact compileFlatTotal_semantics_proofSide (compileProg config decs).1.patternCfg
    relationCfg ffi _ _ _ configs notFail

/-- Source lowering, elimination, and pattern compilation compose to give a
source observation for the production flat output, under the preliminary
factored source invariant. The invariant and semantics still require HOL
correspondence review. -/
theorem factoredCompileTotal_semantics_proofSide {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : State F) (sourceEnv : SemEnv Value) (config : Config)
    (sourceConfig targetConfig : FlatSem.InstallConfig C) (decs : List Dec)
    (precondition : FactoredPrecondition1 interp transform source sourceEnv config sourceConfig decs)
    (relationCfg : FlatPattern.Config)
    (configs : FlatPattern.installConfRel relationCfg sourceConfig targetConfig)
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs .fail) :
    Flapjack.SemanticsHOL.semanticsProg source sourceEnv decs
      (FlatSem.semantics targetConfig source.ffi (compileTotal config decs).2) := by
  have compiled : compileProg config decs =
      ((compileProg config decs).1, (compileProg config decs).2) := by
    cases compileProg config decs
    rfl
  have notFail := factoredCompileProg_semantics_ne_fail interp transform source sourceEnv config
    (compileProg config decs).1 sourceConfig decs (compileProg config decs).2 precondition compiled safe
  have behavior := factoredCompileProg_semantics interp transform source sourceEnv config
    (compileProg config decs).1 sourceConfig decs (compileProg config decs).2 precondition compiled safe
  rw [compileTotal_flat_semantics_proofSide config decs relationCfg source.ffi
    sourceConfig targetConfig configs notFail] at behavior
  exact behavior

/-- The incremental production entry point preserves proof-side observations
across its pattern-compilation stage. Source compilation and HOL correspondence
are separate obligations. -/
theorem incCompile_pattern_semantics {C F : Type}
    (envId : Nat × Nat) (config : Config) (decs : List Flapjack.AstHOL.Dec)
    (relationCfg : FlatPattern.Config) (ffi : HolFfiState F)
    (sourceConfig targetConfig : FlatSem.InstallConfig C)
    (configs : FlatPattern.installConfRel relationCfg sourceConfig targetConfig)
    (notFail : FlatSem.semantics sourceConfig ffi (incCompileProg envId config decs).2 ≠ .fail) :
    FlatSem.semantics sourceConfig ffi (incCompileProg envId config decs).2 =
      FlatSem.semantics targetConfig ffi (incCompile envId config decs).2 := by
  exact FlatPattern.compileDecs_semantics_proofSide relationCfg
    (incCompileProg envId config decs).1.patternCfg ffi _ _ _ configs notFail

end Flapjack.Compiler.Backend.SourceToFlat
