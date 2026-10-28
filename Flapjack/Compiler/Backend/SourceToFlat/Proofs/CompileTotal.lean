import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatElim.Proofs.Reachability

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

end Flapjack.Compiler.Backend.SourceToFlat
