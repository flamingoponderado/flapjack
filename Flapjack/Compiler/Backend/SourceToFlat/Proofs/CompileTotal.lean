import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatElim.Proofs.Reachability

/-! Totality of the bounded source-to-flat pipeline. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Flat elimination always returns, so the bounded source-to-flat pipeline
does not fail. This establishes totality only; pass correspondence is separate. -/
theorem compile_succeeds (config : Config) (decs : List Flapjack.AstHOL.Dec) :
    ∃ result, compile config decs = some result := by
  cases program : compileProg config decs with
  | mk next code =>
    obtain ⟨kept, keptEq⟩ := FlatElim.removeFlatProg_succeeds code
    refine ⟨(next, kept.map (FlatPattern.compileDec next.patternCfg)), ?_⟩
    simp [compile, compileFlat, program, keptEq]

end Flapjack.Compiler.Backend.SourceToFlat
