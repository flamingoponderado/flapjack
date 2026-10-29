import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatElim.Proofs.Reachability
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ProgramSimulation

/-! Totality of the bounded source-to-flat pipeline. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

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
