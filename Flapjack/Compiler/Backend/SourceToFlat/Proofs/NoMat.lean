import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatPattern.Proofs.NoMat

/-! Match-freedom at the source-to-flat pass boundary. These are
Flapjack-side consequences of the pattern compiler, not reviewed HOL ports. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- The normal source-to-flat path produces match-free declarations. -/
theorem noMat_compileTotal (cfg : Config) (program : List AstHOL.Dec) :
    FlatProps.noMatDecs (compileTotal cfg program).2 = true := by
  unfold compileTotal
  cases compiled : compileProg cfg program with
  | mk next code =>
    simpa [compiled, compileFlatTotal] using
      FlatPattern.noMat_compileDecs next.patternCfg (FlatElim.removeFlatProgTotal code)

/-- The incremental path also produces match-free declarations. -/
theorem noMat_incCompile (envId : Nat × Nat) (cfg : Config) (program : List AstHOL.Dec) :
    FlatProps.noMatDecs (incCompile envId cfg program).2 = true := by
  unfold incCompile
  cases compiled : incCompileProg envId cfg program with
  | mk next code =>
    simpa [compiled] using FlatPattern.noMat_compileDecs next.patternCfg code

end Flapjack.Compiler.Backend.SourceToFlat
